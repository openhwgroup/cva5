/*
 * Copyright © 2017-2019 Eric Matthews,  Lesley Shannon
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
import riscv_types::*;
import taiga_types::*;

module decode_and_issue (
        input logic clk,
        input logic rst,

        output logic pre_decode_pop,
        input logic fb_valid,
        input fetch_buffer_packet_t fb,

        tracking_interface.decode ti,
        register_file_issue_interface.issue rf_issue,

        output alu_inputs_t alu_inputs,
        output load_store_inputs_t ls_inputs,
        output branch_inputs_t branch_inputs,
        output gc_inputs_t gc_inputs,
        output mul_inputs_t mul_inputs,
        output div_inputs_t div_inputs,

        unit_issue_interface.decode unit_issue [NUM_UNITS-1:0],

        input logic gc_issue_hold,
        input logic gc_fetch_flush,
        input logic gc_issue_flush,
        output logic gc_flush_required,

        output logic load_store_issue,

        output logic instruction_issued,
        output logic instruction_issued_no_rd,
        output logic instruction_issued_with_rd,
        output logic illegal_instruction,

        //Trace signals
        output logic tr_operand_stall,
        output logic tr_unit_stall,
        output logic tr_no_id_stall,
        output logic tr_no_instruction_stall,
        output logic tr_other_stall,
        output logic tr_branch_operand_stall,
        output logic tr_alu_operand_stall,
        output logic tr_ls_operand_stall,
        output logic tr_div_operand_stall,

        output logic tr_alu_op,
        output logic tr_branch_or_jump_op,
        output logic tr_load_op,
        output logic tr_store_op,
        output logic tr_mul_op,
        output logic tr_div_op,
        output logic tr_misc_op,

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
    logic [4:0] rd_addr;

    logic nop;

    logic issue_valid;
    logic operands_ready;
    logic [NUM_UNITS-1:0] unit_operands_ready;
    logic mult_div_op;

    logic [NUM_WB_UNITS-1:0] unit_needed_for_id_gen;
    logic [WB_UNITS_WIDTH-1:0] unit_needed_for_id_gen_int;
    logic [NUM_UNITS-1:0] unit_needed;
    logic [NUM_UNITS-1:0] unit_ready;
    logic [NUM_UNITS-1:0] issue_ready;
    logic [NUM_UNITS-1:0] issue;

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Instruction Buffer
    assign pre_decode_pop = instruction_issued;

    assign uses_rs1 = fb.uses_rs1;
    assign uses_rs2 = fb.uses_rs2;
    assign uses_rd = fb.uses_rd;

    //Instruction aliases
    assign opcode = fb.instruction[6:0];
    assign opcode_trim = opcode[6:2];
    assign fn3 = fb.instruction[14:12];
    assign rs1_addr = fb.instruction[19:15];
    assign rs2_addr = fb.instruction[24:20];
    assign rd_addr = fb.instruction[11:7];


    assign rd_zero = ~|rd_addr;
    assign nop = (opcode_trim inside {LUI_T, AUIPC_T, ARITH_T, ARITH_IMM_T} && rd_zero);

    ////////////////////////////////////////////////////
    //Register File interface inputs
    assign rf_issue.rs1_addr = rs1_addr;
    assign rf_issue.rs2_addr = rs2_addr;
    assign rf_issue.rd_addr = rd_addr;
    assign rf_issue.instruction_issued = instruction_issued_with_rd & ~rd_zero;
    assign rf_issue.id = ti.issue_id;
    assign rf_issue.uses_rs1 = uses_rs1;
    assign rf_issue.uses_rs2 = uses_rs2;

    ////////////////////////////////////////////////////
    //Tracking Interface
    //CSR results are passed through the load/store output
    always_comb begin
        unit_needed_for_id_gen = unit_needed[NUM_WB_UNITS-1:0];
        unit_needed_for_id_gen[LS_UNIT_WB_ID] |= (unit_needed[GC_UNIT_ID] & is_csr);
    end
    one_hot_to_integer #(NUM_WB_UNITS) unit_id_gen (.*, .one_hot(unit_needed_for_id_gen), .int_out(unit_needed_for_id_gen_int));

    assign ti.inflight_packet.rd_addr = rd_addr;
    assign ti.inflight_packet.is_store = is_store;
    assign ti.issued = instruction_issued & (uses_rd | unit_needed[LS_UNIT_WB_ID]);
    assign ti.issue_unit_id = unit_needed_for_id_gen_int;
    assign ti.exception_possible = opcode_trim inside {LOAD_T, STORE_T, AMO_T};
    ////////////////////////////////////////////////////
    //Unit Determination
    assign mult_div_op = fb.instruction[25];

    assign unit_needed[BRANCH_UNIT_ID] = opcode_trim inside {BRANCH_T, JAL_T, JALR_T};
    assign unit_needed[ALU_UNIT_WB_ID] = fb.alu_request;
    assign unit_needed[LS_UNIT_WB_ID] = opcode_trim inside {LOAD_T, STORE_T, AMO_T};
    assign unit_needed[GC_UNIT_ID] = opcode_trim inside {SYSTEM_T, FENCE_T};

    generate if (USE_MUL)
            assign unit_needed[MUL_UNIT_WB_ID] = (opcode_trim == ARITH_T) && mult_div_op && ~fn3[2];
    endgenerate

    generate if (USE_DIV)
            assign unit_needed[DIV_UNIT_WB_ID] = (opcode_trim == ARITH_T) && mult_div_op && fn3[2];
    endgenerate

    ////////////////////////////////////////////////////
    //Unit ready
    generate
        for (i=0; i<NUM_UNITS; i++) begin
            assign unit_ready[i] = unit_issue[i].ready;
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Issue Determination
    assign issue_valid = fb_valid & ti.id_available & ~gc_issue_hold & ~gc_fetch_flush;

    assign operands_ready = ~rf_issue.rs1_conflict & ~rf_issue.rs2_conflict;

    //All units share the same operand ready logic except load-store which has an internal forwarding path
    always_comb begin
        unit_operands_ready = {NUM_UNITS{operands_ready}};
        unit_operands_ready[LS_UNIT_WB_ID] = ~rf_issue.rs1_conflict;
    end

    assign issue_ready = unit_needed & unit_ready;
    assign issue = {NUM_UNITS{issue_valid}} & unit_operands_ready & issue_ready;

    assign instruction_issued = issue_valid & |(unit_operands_ready & issue_ready);
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
            default : alu_rs1_data = rf_issue.rs1_data; //ALU_RS1_RF
        endcase

        case(fb.alu_rs2_sel)
            ALU_RS2_LUI_AUIPC : alu_rs2_data = {fb.instruction[31:12], 12'b0};
            ALU_RS2_ARITH_IMM : alu_rs2_data = 32'(signed'(fb.instruction[31:20]));
            ALU_RS2_JAL_JALR : alu_rs2_data = 4;
            ALU_RS2_RF : alu_rs2_data = rf_issue.rs2_data;
        endcase
    end

    assign alu_inputs.in1 = {(rf_issue.rs1_data[XLEN-1] & ~fn3[0]), alu_rs1_data};//(fn3[0]  is SLTU_fn3);
    assign alu_inputs.in2 = {(alu_rs2_data[XLEN-1] & ~fn3[0]), alu_rs2_data};
    assign alu_inputs.shifter_in = rf_issue.rs1_data;
    assign alu_inputs.shift_amount = opcode[5] ? rf_issue.rs2_data[4:0] : rs2_addr;
    assign alu_inputs.subtract = fb.alu_sub;
    assign alu_inputs.arith = alu_rs1_data[XLEN-1] & fb.instruction[30];//shift in bit
    assign alu_inputs.lshift = ~fn3[2];
    assign alu_inputs.logic_op = fb.alu_logic_op;
    assign alu_inputs.shifter_path = ~(opcode[2] | fn3 inside {SLT_fn3, SLTU_fn3, XOR_fn3, OR_fn3, AND_fn3, ADD_SUB_fn3}); //opcode[2] LUI AUIPC JAL JALR
    assign alu_inputs.slt_path = ~opcode[2] & fn3 inside {SLT_fn3, SLTU_fn3};

    ////////////////////////////////////////////////////
    //Load Store unit inputs
    logic [11:0] ls_offset;
    logic is_load;
    logic is_store;
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

    assign is_load = (opcode_trim inside {LOAD_T, AMO_T}) && !(amo_op & store_conditional); //LR and AMO_ops perform a read operation as well
    assign is_store = (opcode_trim == STORE_T) || (amo_op && store_conditional);//Used for LS unit and for ID tracking
    assign ls_offset = opcode[5] ? {fb.instruction[31:25], fb.instruction[11:7]} : fb.instruction[31:20];

    assign ls_inputs.rs1 = rf_issue.rs1_data;
    assign ls_inputs.rs2 = rf_issue.rs2_data;
    assign ls_inputs.offset = ls_offset;
    assign ls_inputs.pc = fb.pc;
    assign ls_inputs.fn3 = amo_op ? LS_W_fn3 : fn3;
    assign ls_inputs.load = is_load;
    assign ls_inputs.store = is_store;
    assign ls_inputs.forwarded_store = rf_issue.rs2_conflict;
    assign ls_inputs.store_forward_id = rf_issue.rs2_id;

    ////////////////////////////////////////////////////
    //Branch unit inputs
    assign branch_inputs.rs1 = rf_issue.rs1_data;
    assign branch_inputs.rs2 = rf_issue.rs2_data;
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
    logic is_csr;
    assign sfence = fb.instruction[25];
    assign ifence =  (opcode_trim == FENCE_T) && fn3[0];
    assign environment_op = (opcode_trim == SYSTEM_T) && (fn3 == 0);
    assign is_csr = (opcode_trim == SYSTEM_T) && (fn3 != 0);

    assign gc_inputs.pc = fb.pc;
    assign gc_inputs.instruction = fb.instruction;
    assign gc_inputs.rs1 = rf_issue.rs1_data;
    assign gc_inputs.rs2 = rf_issue.rs2_data;
    assign gc_inputs.is_fence = (opcode_trim == FENCE_T) && ~fn3[0];
    assign gc_inputs.is_i_fence = issue[GC_UNIT_ID] && ifence;
    assign gc_inputs.is_csr = is_csr;

    assign gc_inputs.is_ecall = environment_op && (fb.instruction[21:20] == 0);
    assign gc_inputs.is_ebreak = environment_op && (fb.instruction[21:20] == 2'b01);
    assign gc_inputs.is_ret = environment_op && (fb.instruction[21:20] == 2'b10);

    assign gc_flush_required = issue[GC_UNIT_ID] && (environment_op | ifence);

    ////////////////////////////////////////////////////
    //Mul unit inputs
    generate if (USE_MUL) begin
            assign mul_inputs.rs1 = rf_issue.rs1_data;
            assign mul_inputs.rs2 = rf_issue.rs2_data;
            assign mul_inputs.op = fn3[1:0];
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Div unit inputs
    generate if (USE_DIV) begin
            logic [4:0] prev_div_rs1_addr;
            logic [4:0] prev_div_rs2_addr;
            logic prev_div_result_valid;
            logic set_prev_div_result_valid;
            logic clear_prev_div_result_valid;
            logic current_op_resuses_rs1_rs2;

            always_ff @(posedge clk) begin
                if (issue[DIV_UNIT_WB_ID]) begin
                    prev_div_rs1_addr <= rs1_addr;
                    prev_div_rs2_addr <= rs2_addr;
                end
            end

            assign current_op_resuses_rs1_rs2 = (prev_div_rs1_addr == rs1_addr) && (prev_div_rs2_addr == rs2_addr);
            assign set_prev_div_result_valid = unit_needed[DIV_UNIT_WB_ID];

            //If current div operation overwrites an input register OR any other instruction overwrites the last div operations input registers
            assign clear_prev_div_result_valid = uses_rd & ((rd_addr == (unit_needed[DIV_UNIT_WB_ID] ? rs1_addr : prev_div_rs1_addr)) || (rd_addr == (unit_needed[DIV_UNIT_WB_ID] ? rs2_addr : prev_div_rs2_addr)));

            set_clr_reg_with_rst #(.SET_OVER_CLR(0), .WIDTH(1), .RST_VALUE(0)) prev_div_result_valid_m (
              .clk, .rst,
              .set(instruction_issued & set_prev_div_result_valid),
              .clr(instruction_issued & clear_prev_div_result_valid),
              .result(prev_div_result_valid)
            );

            assign div_inputs.rs1 = rf_issue.rs1_data;
            assign div_inputs.rs2 = rf_issue.rs2_data;
            assign div_inputs.op = fn3[1:0];
            assign div_inputs.reuse_result = prev_div_result_valid & current_op_resuses_rs1_rs2;
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Unit EX signals
    generate
        for (i = 0; i < NUM_UNITS; i++) begin
            assign unit_issue[i].possible_issue = unit_needed[i] & unit_operands_ready[i] & fb_valid & ti.id_available & ~gc_issue_hold;
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
    generate if (ENABLE_TRACE_INTERFACE) begin
        assign tr_operand_stall = |(unit_needed & unit_ready) & issue_valid & ~|(unit_operands_ready & issue_ready);
        assign tr_unit_stall = ~|(unit_needed & unit_ready) & issue_valid & |(unit_operands_ready & issue_ready);
        assign tr_no_id_stall = |(unit_needed & unit_ready) & (fb_valid & ~ti.id_available & ~gc_issue_hold & ~gc_fetch_flush) & |(unit_operands_ready & issue_ready);
        assign tr_no_instruction_stall = ~fb_valid | gc_fetch_flush;
        assign tr_other_stall = fb_valid & ~instruction_issued & ~(tr_operand_stall | tr_unit_stall | tr_no_id_stall | tr_no_instruction_stall);
        assign tr_branch_operand_stall = tr_operand_stall & unit_needed[BRANCH_UNIT_ID];
        assign tr_alu_operand_stall = tr_operand_stall & unit_needed[ALU_UNIT_WB_ID] & ~unit_needed[BRANCH_UNIT_ID];
        assign tr_ls_operand_stall = tr_operand_stall & unit_needed[LS_UNIT_WB_ID];
        assign tr_div_operand_stall = tr_operand_stall & unit_needed[DIV_UNIT_WB_ID];

        //Instruction Mix
        assign tr_alu_op = instruction_issued && (opcode_trim inside {ARITH_T, ARITH_IMM_T, AUIPC_T, LUI_T} && ~tr_mul_op && ~tr_div_op);
        assign tr_branch_or_jump_op = instruction_issued && (opcode_trim inside {JAL_T, JALR_T, BRANCH_T});
        assign tr_load_op = instruction_issued && (opcode_trim inside {LOAD_T, AMO_T});
        assign tr_store_op = instruction_issued && (opcode_trim inside {STORE_T});
        assign tr_mul_op = instruction_issued && unit_needed[MUL_UNIT_WB_ID];
        assign tr_div_op = instruction_issued && unit_needed[DIV_UNIT_WB_ID];
        assign tr_misc_op = instruction_issued & ~(tr_alu_op | tr_branch_or_jump_op | tr_load_op | tr_store_op | tr_mul_op | tr_div_op);

        assign tr_instruction_issued_dec = instruction_issued;
        assign tr_instruction_pc_dec = fb.pc;
        assign tr_instruction_data_dec = fb.instruction;
    end
    endgenerate

endmodule
