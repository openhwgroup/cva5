/*
 * Copyright © 2017, 2018, 2019 Eric Matthews,  Lesley Shannon
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * Initial code developed under the supervision of Dr. Lesley Shannon,
 * Reconfigurable Computing Lab, Simon Fraser University.
 *
 * Author(s):
 *             Eric Matthews <ematthew@sfu.ca>
 */

import taiga_config::*;
import taiga_types::*;

module decode(
        input logic clk,
        input logic rst,

        output logic pre_decode_pop,
        input logic fb_valid,
        input fetch_buffer_packet_t fb,

        tracking_interface.decode ti,
        register_file_decode_interface.decode rf_decode,

        output alu_inputs_t alu_inputs,
        output load_store_inputs_t ls_inputs,
        output branch_inputs_t branch_inputs,
        output gc_inputs_t gc_inputs,
        output mul_inputs_t mul_inputs,
        output  div_inputs_t div_inputs,

        unit_issue_interface.decode unit_issue [NUM_UNITS-1:0],

        input logic gc_issue_hold,
        input logic gc_fetch_flush,
        input logic gc_issue_flush,
        output logic gc_flush_required,

        output logic load_store_issue,

        output logic instruction_issued_no_rd,
        output logic instruction_issued_with_rd,
        output logic illegal_instruction,

        //Trace signals
        output logic tr_operand_stall,
        output logic tr_unit_stall,
        output logic tr_no_id_stall,
        output logic tr_no_instruction_stall,
        output logic tr_other_stall,

        output logic tr_instruction_issued_dec,
        output logic [31:0] tr_instruction_pc_dec,
        output logic [31:0] tr_instruction_data_dec
        );

    logic [2:0] fn3;
    logic [6:0] opcode;
    logic [4:0] opcode_trim;

    logic uses_rs1;
    logic uses_rs2;
    logic uses_rd;
    logic rd_zero;

    logic [4:0] rs1_addr;
    logic [4:0] rs2_addr;
    logic [4:0] future_rd_addr;
    unit_id_t unit_id;

    logic nop;

    logic  register_in_use_by_load_op [31:0];

    logic store_data_in_use_by_load_op;
    logic load_store_forward_possible;

    logic issue_valid;
    logic load_store_operands_ready;
    logic operands_ready;
    logic [NUM_UNITS-1:0] unit_operands_ready;
    logic mult_div_op;

    logic [NUM_WB_UNITS-1:0] new_request_for_id_gen;
    logic [NUM_UNITS-1:0] new_request;
    logic [NUM_UNITS-1:0] issue_ready;
    logic [NUM_UNITS-1:0] issue;

    logic instruction_issued;
    logic valid_opcode;

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation


    ////////////////////////////////////////////////////
    //Instruction Buffer / Instruction aliases
    assign pre_decode_pop = instruction_issued;

    assign opcode = fb.instruction[6:0];
    assign opcode_trim = opcode[6:2];
    assign fn3 = fb.instruction[14:12];

    assign uses_rs1 = fb.uses_rs1;
    assign uses_rs2 = fb.uses_rs2;
    assign uses_rd = fb.uses_rd;
    assign rd_zero = fb.rd_zero;

    assign rs1_addr = fb.instruction[19:15];
    assign rs2_addr = fb.instruction[24:20];
    assign future_rd_addr = fb.instruction[11:7];
    assign nop = (opcode_trim inside {LUI_T, AUIPC_T, ARITH_T, ARITH_IMM_T} && rd_zero);

    ////////////////////////////////////////////////////
    //Register File interface inputs
    assign rf_decode.rs1_addr  =  rs1_addr;
    assign rf_decode.rs2_addr  =  rs2_addr;
    assign rf_decode.future_rd_addr  =  future_rd_addr;
    assign rf_decode.instruction_issued = instruction_issued_with_rd & ~rd_zero;
    assign rf_decode.id = ti.issue_id;
    assign rf_decode.unit_id = unit_id;
    assign rf_decode.uses_rs1 = uses_rs1;
    assign rf_decode.uses_rs2 = uses_rs2;


    ////////////////////////////////////////////////////
    //Tracking Interface
    always_comb begin
        new_request_for_id_gen = new_request[NUM_WB_UNITS-1:0];
        new_request_for_id_gen[LS_UNIT_WB_ID] |= new_request[GC_UNIT_ID];
    end

    one_hot_to_integer #(NUM_WB_UNITS) new_request_to_int (.*, .one_hot(new_request_for_id_gen), .int_out(unit_id));

    assign ti.inflight_packet.rd_addr = future_rd_addr;
    assign ti.inflight_packet.rd_addr_nzero = ~rd_zero;
    assign ti.inflight_packet.is_store = (opcode_trim == STORE_T) || (amo_op && store_conditional);
    assign ti.inflight_packet.id = ti.issue_id;
    assign ti.inflight_packet.unit_id = unit_id;
    assign ti.issued = instruction_issued & (uses_rd | new_request[LS_UNIT_WB_ID]);

    ////////////////////////////////////////////////////
    //Unit Determination
    assign mult_div_op = fb.instruction[25];

    assign new_request[BRANCH_UNIT_ID] = opcode_trim inside {BRANCH_T, JAL_T, JALR_T};
    assign new_request[ALU_UNIT_WB_ID] = fb.alu_request;
    assign new_request[LS_UNIT_WB_ID] = opcode_trim inside {LOAD_T, STORE_T, AMO_T};
    assign new_request[GC_UNIT_ID] = opcode_trim inside {SYSTEM_T, FENCE_T};

    generate if (USE_MUL)
            assign new_request[MUL_UNIT_WB_ID] = (opcode_trim == ARITH_T) && mult_div_op && ~fn3[2];
    endgenerate

    generate if (USE_DIV)
            assign new_request[DIV_UNIT_WB_ID] = (opcode_trim == ARITH_T) && mult_div_op && fn3[2];
    endgenerate

    assign valid_opcode = opcode_trim inside {BRANCH_T, JAL_T, JALR_T, ARITH_T, ARITH_IMM_T, AUIPC_T, LUI_T, LOAD_T, STORE_T, AMO_T, SYSTEM_T, FENCE_T};

    ////////////////////////////////////////////////////
    //Unit ready
    generate
        for (i=0; i<NUM_UNITS; i++) begin
            assign issue_ready[i] = new_request[i] & unit_issue[i].ready;
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Issue Determination
    assign issue_valid = fb_valid & ti.id_available & ~gc_issue_hold & ~gc_fetch_flush;

    assign operands_ready = ~rf_decode.rs1_conflict & ~rf_decode.rs2_conflict;
    assign load_store_operands_ready =  ~rf_decode.rs1_conflict & (~rf_decode.rs2_conflict | (rf_decode.rs2_conflict & load_store_forward_possible));

    //All units share the same operand ready logic except load-store which has an internal forwarding path
    always_comb begin
        unit_operands_ready = {NUM_UNITS{operands_ready}};
        unit_operands_ready[LS_UNIT_WB_ID] = load_store_operands_ready;
    end

    assign issue = {NUM_UNITS{issue_valid}} & unit_operands_ready & issue_ready;

    assign instruction_issued =
        ((LS_INPUT_BUFFER_DEPTH >= MAX_INFLIGHT_COUNT) &&
        (DIV_INPUT_BUFFER_DEPTH >= MAX_INFLIGHT_COUNT)) ?
        (valid_opcode & issue_valid & load_store_operands_ready) :
        ((|issue_ready) & issue_valid & load_store_operands_ready);

    assign instruction_issued_no_rd = instruction_issued & ~uses_rd;
    assign instruction_issued_with_rd = instruction_issued & uses_rd;

    //Decode outputs
    assign load_store_issue = issue[LS_UNIT_WB_ID];

    ////////////////////////////////////////////////////
    //ALU unit inputs
    logic [XLEN-1:0] alu_rs1_data;
    logic [XLEN-1:0] alu_rs2_data;

    always_comb begin
        case(fb.alu_rs1_sel)
            ALU_RS1_ZERO : alu_rs1_data = '0;
            ALU_RS1_PC : alu_rs1_data = fb.pc;
            default : alu_rs1_data = rf_decode.rs1_data; //ALU_RS1_RF
        endcase

        case(fb.alu_rs2_sel)
            ALU_RS2_LUI_AUIPC : alu_rs2_data = {fb.instruction[31:12], 12'b0};
            ALU_RS2_ARITH_IMM : alu_rs2_data = 32'(signed'(fb.instruction[31:20]));
            ALU_RS2_JAL_JALR : alu_rs2_data = 4;
            ALU_RS2_RF : alu_rs2_data = rf_decode.rs2_data;
        endcase
    end

    assign alu_inputs.in1 = {(alu_rs1_data[XLEN-1] & ~fn3[0]), alu_rs1_data};//(fn3[0]  is SLTU_fn3);
    assign alu_inputs.in2 = {(alu_rs2_data[XLEN-1] & ~fn3[0]), alu_rs2_data};
    assign alu_inputs.shifter_in = rf_decode.rs1_data;
    assign alu_inputs.subtract = fb.alu_sub;
    assign alu_inputs.arith = alu_rs1_data[XLEN-1] & fb.instruction[30];//shift in bit
    assign alu_inputs.lshift = ~fn3[2];
    assign alu_inputs.logic_op = fb.alu_logic_op;
    assign alu_inputs.op = fb.alu_op;

    ////////////////////////////////////////////////////
    //Load Store unit inputs
    logic [11:0] ls_offset;
    logic ls_is_load;

    logic amo_op;
    logic store_conditional;
    logic load_reserve;
    logic [4:0] amo_type;

    assign amo_op =  USE_AMO ? (opcode_trim == AMO_T) : 1'b0;
    assign amo_type = fb.instruction[31:27];
    assign store_conditional = (amo_type == AMO_SC);
    assign load_reserve = (amo_type == AMO_LR);

    generate if (USE_AMO) begin
            assign ls_inputs.amo.is_lr = load_reserve;
            assign ls_inputs.amo.is_sc = store_conditional;
            assign ls_inputs.amo.is_amo = amo_op & ~(load_reserve | store_conditional);
            assign ls_inputs.amo.op = amo_type;
        end
        else begin
            assign ls_inputs.amo = '0;
        end
    endgenerate

    assign ls_is_load = (opcode_trim inside {LOAD_T, AMO_T}) && !(amo_op & store_conditional); //LR and AMO_ops perform a read operation as well
    assign ls_offset = opcode[5] ? {fb.instruction[31:25], fb.instruction[11:7]} : fb.instruction[31:20];

    assign ls_inputs.offset = ls_offset;
    assign ls_inputs.virtual_address = rf_decode.rs1_data + 32'(signed'(ls_offset));
    assign ls_inputs.rs2 = rf_decode.rs2_data;
    assign ls_inputs.pc = fb.pc;
    assign ls_inputs.fn3 = amo_op ? LS_W_fn3 : fn3;
    assign ls_inputs.load = ls_is_load;
    assign ls_inputs.store = (opcode_trim == STORE_T) || (amo_op && store_conditional);
    assign ls_inputs.load_store_forward = rf_decode.rs2_conflict;
    assign ls_inputs.instruction_id = ti.issue_id;

    //Last store RD tracking for Load-Store data forwarding
    logic [4:0] last_load_rd;
    logic basic_load;

    assign basic_load = (opcode_trim == LOAD_T);
    always_ff @ (posedge clk) begin
        if (issue[LS_UNIT_WB_ID] & basic_load)
            last_load_rd <= future_rd_addr;
    end

    always_ff @ (posedge clk) begin
       if (instruction_issued)
           register_in_use_by_load_op[future_rd_addr] <= new_request[LS_UNIT_WB_ID] & basic_load;
    end

    assign store_data_in_use_by_load_op = register_in_use_by_load_op[rs2_addr];
    assign load_store_forward_possible = (opcode_trim == STORE_T) && store_data_in_use_by_load_op && (last_load_rd == rs2_addr);

    ////////////////////////////////////////////////////
    //Branch unit inputs
    assign branch_inputs.rs1 = rf_decode.rs1_data;
    assign branch_inputs.rs2 = rf_decode.rs2_data;
    assign branch_inputs.fn3 = fn3;
    assign branch_inputs.dec_pc = fb.pc;
    assign branch_inputs.dec_pc_valid = fb_valid;
    assign branch_inputs.use_signed = !(fn3 inside {BLTU_fn3, BGEU_fn3});
    assign branch_inputs.jal = opcode[3];//(opcode == JAL);
    assign branch_inputs.jalr = ~opcode[3] & opcode[2];//(opcode == JALR);
    assign branch_inputs.is_call = fb.is_call;
    assign branch_inputs.is_return = fb.is_return;
    assign branch_inputs.instruction = fb.instruction;
    assign branch_inputs.branch_metadata = fb.branch_metadata;
    assign branch_inputs.branch_prediction_used = fb.branch_prediction_used;
    assign branch_inputs.bp_update_way = fb.bp_update_way;

    ////////////////////////////////////////////////////
    //Global Control unit inputs
    logic sfence;
    logic ifence;
    logic environment_op;
    assign sfence = fb.instruction[25];
    assign ifence =  (opcode_trim == FENCE_T) && fn3[0];
    assign environment_op = (opcode_trim == SYSTEM_T) && (fn3 == 0);

    always_ff @(posedge clk) begin
        if (issue[GC_UNIT_ID]) begin
            gc_inputs.pc <= fb.pc;
            gc_inputs.instruction <= fb.instruction;
            gc_inputs.rs1 <= rf_decode.rs1_data;
            gc_inputs.rs2 <= rf_decode.rs2_data;
            gc_inputs.rd_is_zero <= rd_zero;
            gc_inputs.is_fence <= (opcode_trim == FENCE_T) && ~fn3[0];
            gc_inputs.is_csr <= (opcode_trim == SYSTEM_T) && (fn3 != 0);
        end
        gc_inputs.is_ecall <= issue[GC_UNIT_ID] && environment_op && (fb.instruction[21:20] == 0);
        gc_inputs.is_ebreak <= issue[GC_UNIT_ID] && environment_op && (fb.instruction[21:20] == 2'b01);
        gc_inputs.is_ret <= issue[GC_UNIT_ID] && environment_op && (fb.instruction[21:20] == 2'b10);
        gc_inputs.is_i_fence <= issue[GC_UNIT_ID] && ifence;
    end
    assign gc_flush_required = issue[GC_UNIT_ID] && (environment_op | ifence);


    ////////////////////////////////////////////////////
    //Mul unit inputs
    generate if (USE_MUL) begin
            assign mul_inputs.rs1 = rf_decode.rs1_data;
            assign mul_inputs.rs2 = rf_decode.rs2_data;
            assign mul_inputs.op = fn3[1:0];
        end
    endgenerate


    ////////////////////////////////////////////////////
    //Div unit inputs
    generate if (USE_DIV) begin
            logic [4:0] prev_div_rs1_addr;
            logic [4:0] prev_div_rs2_addr;
            logic prev_div_result_valid;
            logic prev_div_result_valid_r;
            //If a subsequent div request uses the same inputs then
            //don't rerun div operation
            logic div_rd_overwrites_rs1_or_rs2;
            logic rd_overwrites_previously_saved_rs1_or_rs2;
            logic current_op_resuses_rs1_rs2;

            always_ff @(posedge clk) begin
                if (issue[DIV_UNIT_WB_ID]) begin
                    prev_div_rs1_addr <= rs1_addr;
                    prev_div_rs2_addr <= rs2_addr;
                end
            end

            assign div_rd_overwrites_rs1_or_rs2 = (future_rd_addr == rs1_addr || future_rd_addr == rs2_addr);
            assign rd_overwrites_previously_saved_rs1_or_rs2 = (future_rd_addr == prev_div_rs1_addr || future_rd_addr == prev_div_rs2_addr);
            assign current_op_resuses_rs1_rs2 = (prev_div_rs1_addr == rs1_addr) && (prev_div_rs2_addr == rs2_addr);

            always_comb begin
                prev_div_result_valid = prev_div_result_valid_r;
                if (new_request[DIV_UNIT_WB_ID])
                    prev_div_result_valid = ~div_rd_overwrites_rs1_or_rs2;
                else if (uses_rd & rd_overwrites_previously_saved_rs1_or_rs2)
                    prev_div_result_valid = 0;
            end

            always_ff @(posedge clk) begin
                if (rst)
                    prev_div_result_valid_r <= 0;
                else if (instruction_issued)
                    prev_div_result_valid_r <= prev_div_result_valid;
            end

            assign div_inputs.rs1 = rf_decode.rs1_data;
            assign div_inputs.rs2 = rf_decode.rs2_data;
            assign div_inputs.op = fn3[1:0];
            assign div_inputs.reuse_result = prev_div_result_valid_r & current_op_resuses_rs1_rs2;
            assign div_inputs.instruction_id = ti.issue_id;
        end
    endgenerate


    ////////////////////////////////////////////////////
    //Unit EX signals
    generate
        for(i = 0; i < NUM_UNITS; i++) begin
            assign unit_issue[i].possible_issue = new_request[i] & ti.id_available;
            assign unit_issue[i].new_request = issue[i];
            assign unit_issue[i].instruction_id = ti.issue_id;
            always_ff @(posedge clk) begin
                unit_issue[i].new_request_r <= issue[i];
            end
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Illegal Opcode check
    always_comb begin
        illegal_instruction = !(opcode inside {LUI, AUIPC, JAL, JALR, BRANCH, LOAD, STORE, ARITH, ARITH_IMM, FENCE, AMO, SYSTEM});
        if (opcode == ARITH) begin
            if (!USE_MUL && !USE_DIV)
                illegal_instruction = fb.instruction[25];
            else if (!USE_MUL && USE_DIV)
                illegal_instruction = fb.instruction[25] & ~fn3[2];
            else if (!USE_MUL && !USE_DIV)
                illegal_instruction = fb.instruction[25] & fn3[2];
            else
                illegal_instruction = 0;
        end
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////
    //Trace Interface
    assign tr_operand_stall = (|issue_ready) & issue_valid & ~load_store_operands_ready;
    assign tr_unit_stall = ~(|issue_ready) & issue_valid & load_store_operands_ready;
    assign tr_no_id_stall = (|issue_ready) & (fb_valid & ~ti.id_available & ~gc_issue_hold & ~gc_fetch_flush) & load_store_operands_ready;
    assign tr_no_instruction_stall = ~fb_valid;
    assign tr_other_stall = fb_valid & ~instruction_issued & ~(tr_operand_stall | tr_unit_stall | tr_no_id_stall | tr_no_instruction_stall) & ~gc_fetch_flush;

    assign tr_instruction_issued_dec = instruction_issued;
    assign tr_instruction_pc_dec = fb.pc;
    assign tr_instruction_data_dec = fb.instruction;


endmodule
