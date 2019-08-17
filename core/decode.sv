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

        instruction_buffer_interface.decode ib,
        tracking_interface.decode ti,
        register_file_decode_interface.decode rf_decode,

        output alu_inputs_t alu_inputs,
        output load_store_inputs_t ls_inputs,
        output branch_inputs_t branch_inputs,
        output gc_inputs_t gc_inputs,
        output mul_inputs_t mul_inputs,
        output  div_inputs_t div_inputs,

        func_unit_ex_interface.decode alu_ex,
        func_unit_ex_interface.decode ls_ex,
        func_unit_ex_interface.decode branch_ex,
        func_unit_ex_interface.decode gc_ex,
        func_unit_ex_interface.decode mul_ex,
        func_unit_ex_interface.decode div_ex,

        input logic gc_issue_hold,
        input logic gc_fetch_flush,
        input logic gc_issue_flush,

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

    logic nop;

    logic  register_in_use_by_load_op [31:0];

    logic store_data_in_use_by_load_op;
    logic load_store_forward_possible;

    logic issue_valid;
    logic load_store_operands_ready;
    logic operands_ready;

    logic mult_div_op;

    logic [NUM_WB_UNITS-1:0] new_request;
    logic [WB_UNITS_WIDTH-1:0] new_request_int;
    logic [NUM_WB_UNITS-1:0] issue_ready;
    logic [NUM_WB_UNITS-1:0] issue;

    logic store_issued;
    logic instruction_issued;

    instruction_id_t last_id;

    ////////////////////////////////////////////////////
    //Implementation


    ////////////////////////////////////////////////////
    //Instruction Buffer / Instruction aliases
    assign ib.pop = instruction_issued;

    assign opcode = ib.data_out.instruction[6:0];
    assign opcode_trim = opcode[6:2];
    assign fn3 = ib.data_out.instruction[14:12];

    assign uses_rs1 = ib.data_out.uses_rs1;
    assign uses_rs2 = ib.data_out.uses_rs2;
    assign uses_rd = ib.data_out.uses_rd;
    assign rd_zero = ib.data_out.rd_zero;

    assign rs1_addr = ib.data_out.instruction[19:15];
    assign rs2_addr = ib.data_out.instruction[24:20];
    assign future_rd_addr = ib.data_out.instruction[11:7];
    assign nop = (opcode_trim inside {LUI_T, AUIPC_T, ARITH_T, ARITH_IMM_T} && rd_zero);

    ////////////////////////////////////////////////////
    //Register File interface inputs
    assign rf_decode.rs1_addr  =  rs1_addr;
    assign rf_decode.rs2_addr  =  rs2_addr;
    assign rf_decode.future_rd_addr  =  future_rd_addr;
    assign rf_decode.instruction_issued = instruction_issued_with_rd & ~rd_zero;
    assign rf_decode.id = ti.issue_id;
    assign rf_decode.uses_rs1 = uses_rs1;
    assign rf_decode.uses_rs2 = uses_rs2;


    ////////////////////////////////////////////////////
    //Tracking Interface
    assign ti.inflight_packet.unit_id = new_request;
    assign ti.inflight_packet.rd_addr = future_rd_addr;
    assign ti.inflight_packet.rd_addr_nzero = ~rd_zero;
    assign ti.issued = instruction_issued_with_rd | store_issued;

    ////////////////////////////////////////////////////
    //Unit Determination
    assign mult_div_op = ib.data_out.instruction[25];

    assign new_request[BRANCH_UNIT_WB_ID] = opcode_trim inside {BRANCH_T, JAL_T, JALR_T};
    assign new_request[ALU_UNIT_WB_ID] =  ((opcode_trim == ARITH_T)  && ~mult_div_op) || opcode_trim inside {ARITH_IMM_T, AUIPC_T, LUI_T};
    assign new_request[LS_UNIT_WB_ID] = opcode_trim inside {LOAD_T, STORE_T, AMO_T};
    assign new_request[GC_UNIT_WB_ID] = opcode_trim inside {SYSTEM_T, FENCE_T};

    generate if (USE_MUL)
            assign new_request[MUL_UNIT_WB_ID] = (opcode_trim == ARITH_T) && mult_div_op && ~fn3[2];
    endgenerate

    generate if (USE_DIV)
            assign new_request[DIV_UNIT_WB_ID] = (opcode_trim == ARITH_T) && mult_div_op && fn3[2];
    endgenerate


    ////////////////////////////////////////////////////
    //Unit ready
    assign issue_ready[BRANCH_UNIT_WB_ID] = new_request[BRANCH_UNIT_WB_ID] & (branch_ex.ready | ~uses_rd);
    assign issue_ready[ALU_UNIT_WB_ID] = new_request[ALU_UNIT_WB_ID] & alu_ex.ready;
    assign issue_ready[LS_UNIT_WB_ID] = new_request[LS_UNIT_WB_ID] & ls_ex.ready;
    assign issue_ready[GC_UNIT_WB_ID] = new_request[GC_UNIT_WB_ID] & gc_ex.ready;
    generate if (USE_MUL)
            assign issue_ready[MUL_UNIT_WB_ID] = new_request[MUL_UNIT_WB_ID] & mul_ex.ready;
    endgenerate
    generate if (USE_DIV)
            assign issue_ready[DIV_UNIT_WB_ID] = new_request[DIV_UNIT_WB_ID] & div_ex.ready;
    endgenerate


    ////////////////////////////////////////////////////
    //Issue Determination
    assign issue_valid = ib.valid & ti.id_available & ~gc_issue_hold & ~gc_fetch_flush;

    assign operands_ready = ~rf_decode.rs1_conflict & ~rf_decode.rs2_conflict;
    assign load_store_operands_ready =  ~rf_decode.rs1_conflict & (~rf_decode.rs2_conflict | (rf_decode.rs2_conflict & load_store_forward_possible));

    assign issue[BRANCH_UNIT_WB_ID] = issue_valid & operands_ready & issue_ready[BRANCH_UNIT_WB_ID];
    assign issue[ALU_UNIT_WB_ID] = issue_valid & operands_ready & issue_ready[ALU_UNIT_WB_ID];
    assign issue[LS_UNIT_WB_ID] = issue_valid & load_store_operands_ready & issue_ready[LS_UNIT_WB_ID];
    assign issue[GC_UNIT_WB_ID] = issue_valid & operands_ready &  issue_ready[GC_UNIT_WB_ID];
    generate if (USE_MUL)
            assign issue[MUL_UNIT_WB_ID] = issue_valid & operands_ready & issue_ready[MUL_UNIT_WB_ID];
    endgenerate
    generate if (USE_DIV)
            assign issue[DIV_UNIT_WB_ID] = issue_valid & operands_ready & issue_ready[DIV_UNIT_WB_ID];
    endgenerate

    assign instruction_issued =  (|issue_ready) & issue_valid & load_store_operands_ready;
    assign instruction_issued_no_rd = instruction_issued & ~uses_rd;
    assign instruction_issued_with_rd = instruction_issued & uses_rd;
    assign store_issued = instruction_issued && (opcode_trim == STORE_T);

    //Decode outputs
    assign load_store_issue = issue[LS_UNIT_WB_ID];

    ////////////////////////////////////////////////////
    //ALU unit inputs
    logic [XLEN-1:0] alu_rs1_data;
    logic [XLEN-1:0] alu_rs2_data;
    logic [XLEN-1:0] left_shift_in;

    logic alu_sub;

    logic [1:0] alu_op;
    logic [1:0] alu_logic_op;

    always_comb begin
        if (opcode[2] & opcode[5]) //LUI
            alu_rs1_data = '0;
        else if (opcode[2] & ~opcode[5])//AUIPC
            alu_rs1_data = ib.data_out.pc;
        else
            alu_rs1_data = rf_decode.rs1_data;
    end

    always_comb begin
        if (opcode[2])//LUI or AUIPC
            alu_rs2_data = {ib.data_out.instruction[31:12], 12'b0};
        else if (~opcode[5]) //ARITH_IMM
            alu_rs2_data = 32'(signed'(ib.data_out.instruction[31:20]));
        else// ARITH instructions
            alu_rs2_data = rf_decode.rs2_data;
    end

    always_comb begin
        case (fn3)
            SLT_fn3 : alu_logic_op = ALU_LOGIC_ADD;
            SLTU_fn3 : alu_logic_op = ALU_LOGIC_ADD;
            SLL_fn3 : alu_logic_op = ALU_LOGIC_ADD;
            XOR_fn3 : alu_logic_op = ALU_LOGIC_XOR;
            OR_fn3 : alu_logic_op = ALU_LOGIC_OR;
            AND_fn3 : alu_logic_op = ALU_LOGIC_AND;
            SRA_fn3 : alu_logic_op = ALU_LOGIC_ADD;
            ADD_SUB_fn3 : alu_logic_op = ALU_LOGIC_ADD;
        endcase
    end

    always_comb begin
        case (fn3)
            SLT_fn3 : alu_op = ALU_SLT;
            SLTU_fn3 : alu_op = ALU_SLT;
            SLL_fn3 : alu_op = ALU_LSHIFT;
            XOR_fn3 : alu_op = ALU_ADD_SUB;
            OR_fn3 : alu_op = ALU_ADD_SUB;
            AND_fn3 : alu_op = ALU_ADD_SUB;
            SRA_fn3 : alu_op = ALU_RSHIFT;
            ADD_SUB_fn3 : alu_op = ALU_ADD_SUB;
        endcase
    end

    always_comb begin
        foreach (left_shift_in[i])
            left_shift_in[i] = rf_decode.rs1_data[XLEN-i-1];
    end

    //Add cases: LUI, AUIPC, ADD[I], all logic ops
    //sub cases: SUB, SLT[U][I]
    assign alu_sub = opcode[2] ? 0 : ((fn3 inside {SLTU_fn3, SLT_fn3}) || ((fn3 == ADD_SUB_fn3) && ib.data_out.instruction[30]) && opcode[5]);

    always_ff @(posedge clk) begin
        if (issue_ready[ALU_UNIT_WB_ID]) begin
            alu_inputs.in1 <= {(alu_rs1_data[XLEN-1] & ~fn3[0]), alu_rs1_data};//(fn3[0]  is SLTU_fn3);
            alu_inputs.in2 <= {(alu_rs2_data[XLEN-1] & ~fn3[0]), alu_rs2_data};
            alu_inputs.shifter_in <= fn3[2] ? rf_decode.rs1_data : left_shift_in;
            alu_inputs.subtract <= alu_sub;
            alu_inputs.arith <= alu_rs1_data[XLEN-1] & ib.data_out.instruction[30];//shift in bit
            alu_inputs.lshift <= ~fn3[2];
            alu_inputs.logic_op <= opcode[2] ? ALU_LOGIC_ADD : alu_logic_op;//put LUI and AUIPC through adder path
            alu_inputs.op <= opcode[2] ? ALU_ADD_SUB : alu_op;//put LUI and AUIPC through adder path
        end
    end


    ////////////////////////////////////////////////////
    //Load Store unit inputs
    logic [11:0] ls_offset;
    logic ls_is_load;

    logic amo_op;
    logic store_conditional;
    logic load_reserve;
    logic [4:0] amo_type;

    assign amo_op =  USE_AMO ? (opcode_trim == AMO_T) : 1'b0;
    assign amo_type = ib.data_out.instruction[31:27];
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
    assign ls_offset = opcode[5] ? {ib.data_out.instruction[31:25], ib.data_out.instruction[11:7]} : ib.data_out.instruction[31:20];

    assign ls_inputs.offset = ls_offset;
    assign ls_inputs.virtual_address = rf_decode.rs1_data + 32'(signed'(ls_offset));
    assign ls_inputs.rs2 = rf_decode.rs2_data;
    assign ls_inputs.pc = ib.data_out.pc;
    assign ls_inputs.fn3 = amo_op ? LS_W_fn3 : fn3;
    assign ls_inputs.load = ls_is_load;
    assign ls_inputs.store = (opcode_trim == STORE_T) || (amo_op && store_conditional);
    assign ls_inputs.load_store_forward = (opcode_trim == STORE_T) && rf_decode.rs2_conflict;
    assign ls_inputs.instruction_id = ti.issue_id;

    //Last store RD tracking for Load-Store data forwarding
    logic [4:0] last_load_rd;
    always_ff @ (posedge clk) begin
        if (issue[LS_UNIT_WB_ID] & ls_is_load)
            last_load_rd <= future_rd_addr;
    end

    always_ff @ (posedge clk) begin
       if (instruction_issued_with_rd)
           register_in_use_by_load_op[future_rd_addr] <= new_request[LS_UNIT_WB_ID];
    end

    assign store_data_in_use_by_load_op = register_in_use_by_load_op[rs2_addr];
    assign load_store_forward_possible = (opcode_trim == STORE_T) && store_data_in_use_by_load_op && (last_load_rd == rs2_addr);

    ////////////////////////////////////////////////////
    //Branch unit inputs
    assign branch_inputs.rs1 = rf_decode.rs1_data;
    assign branch_inputs.rs2 = rf_decode.rs2_data;
    assign branch_inputs.fn3 = fn3;
    assign branch_inputs.dec_pc = ib.data_out.pc;
    assign branch_inputs.dec_pc_valid = ib.valid;
    assign branch_inputs.use_signed = !(fn3 inside {BLTU_fn3, BGEU_fn3});
    assign branch_inputs.jal = opcode[3];//(opcode == JAL);
    assign branch_inputs.jalr = ~opcode[3] & opcode[2];//(opcode == JALR);
    assign branch_inputs.uses_rd = uses_rd;//not (future_rd_addr == 0); jal jalr x0
    assign branch_inputs.is_call = ib.data_out.is_call;
    assign branch_inputs.is_return = ib.data_out.is_return;
    assign branch_inputs.instruction = ib.data_out.instruction;
    assign branch_inputs.branch_metadata = ib.data_out.branch_metadata;
    assign branch_inputs.branch_prediction_used = ib.data_out.branch_prediction_used;
    assign branch_inputs.bp_update_way = ib.data_out.bp_update_way;
    ////////////////////////////////////////////////////
    //Global Control unit inputs
    logic sfence;
    logic ifence;
    logic environment_op;
    assign sfence = ib.data_out.instruction[25];
    assign ifence =  (opcode_trim == FENCE_T) && fn3[0];
    assign environment_op = (opcode_trim == SYSTEM_T) && (fn3 == 0);

    always_ff @(posedge clk) begin
        if (issue_ready[GC_UNIT_WB_ID]) begin
            gc_inputs.pc <= ib.data_out.pc;
            gc_inputs.instruction <= ib.data_out.instruction;
            gc_inputs.rs1 <= rf_decode.rs1_data;
            gc_inputs.rs2 <= rf_decode.rs2_data;
            gc_inputs.rd_is_zero <= rd_zero;
            gc_inputs.is_fence <= (opcode_trim == FENCE_T) && ~fn3[0];
            gc_inputs.is_csr <= (opcode_trim == SYSTEM_T) && (fn3 != 0);
        end
        gc_inputs.flush_required <= issue[GC_UNIT_WB_ID] && (environment_op | ifence);
        gc_inputs.is_ecall <= issue[GC_UNIT_WB_ID] && environment_op && (ib.data_out.instruction[21:20] == 0);
        gc_inputs.is_ebreak <= issue[GC_UNIT_WB_ID] && environment_op && (ib.data_out.instruction[21:20] == 2'b01);
        gc_inputs.is_ret <= issue[GC_UNIT_WB_ID] && environment_op && (ib.data_out.instruction[21:20] == 2'b10);
        gc_inputs.is_i_fence <= issue[GC_UNIT_WB_ID] && ifence;
    end


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
    assign alu_ex.new_request_dec = issue[ALU_UNIT_WB_ID];
    assign ls_ex.new_request_dec = issue[LS_UNIT_WB_ID];
    assign branch_ex.new_request_dec = issue[BRANCH_UNIT_WB_ID];
    assign gc_ex.new_request_dec = issue[GC_UNIT_WB_ID];

    always_ff @(posedge clk) begin
        alu_ex.new_request <= issue[ALU_UNIT_WB_ID];
        ls_ex.new_request <= issue[LS_UNIT_WB_ID];
        branch_ex.new_request <= issue[BRANCH_UNIT_WB_ID];
        gc_ex.new_request <= issue[GC_UNIT_WB_ID];
    end

    assign branch_ex.instruction_id = ti.issue_id;
    assign alu_ex.instruction_id = ti.issue_id;
    //Load Store unit stores ID in input FIFO
    assign gc_ex.instruction_id = ti.issue_id;

    generate if (USE_MUL)
            always_ff @(posedge clk) begin
                mul_ex.new_request <= issue[MUL_UNIT_WB_ID];
            end
        assign mul_ex.new_request_dec = issue[MUL_UNIT_WB_ID];
        assign mul_ex.instruction_id = ti.issue_id;
        assign mul_ex.possible_issue = new_request[MUL_UNIT_WB_ID];
    endgenerate
    generate if (USE_DIV)
            always_ff @(posedge clk) begin
                div_ex.new_request <= issue[DIV_UNIT_WB_ID];
            end
        //DIV unit stores ID in input FIFO
        assign div_ex.new_request_dec = issue[DIV_UNIT_WB_ID];
        assign div_ex.possible_issue = new_request[DIV_UNIT_WB_ID];
    endgenerate

    assign branch_ex.possible_issue = new_request[BRANCH_UNIT_WB_ID];
    assign alu_ex.possible_issue = new_request[ALU_UNIT_WB_ID];
    assign ls_ex.possible_issue = new_request[LS_UNIT_WB_ID];
    assign gc_ex.possible_issue = new_request[GC_UNIT_WB_ID];


    ////////////////////////////////////////////////////
    //Illegal Opcode check
    always_comb begin
        illegal_instruction = !(opcode inside {LUI, AUIPC, JAL, JALR, BRANCH, LOAD, STORE, ARITH, ARITH_IMM, FENCE, AMO, SYSTEM});
        if (opcode == ARITH) begin
            if (!USE_MUL && !USE_DIV)
                illegal_instruction = ib.data_out.instruction[25];
            else if (!USE_MUL && USE_DIV)
                illegal_instruction = ib.data_out.instruction[25] & ~fn3[2];
            else if (!USE_MUL && !USE_DIV)
                illegal_instruction = ib.data_out.instruction[25] & fn3[2];
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
    assign tr_no_id_stall = (|issue_ready) & (ib.valid & ~ti.id_available & ~gc_issue_hold & ~gc_fetch_flush) & load_store_operands_ready;
    assign tr_no_instruction_stall = ~ib.valid;
    assign tr_other_stall = ~instruction_issued & ~(tr_operand_stall | tr_unit_stall | tr_no_id_stall | tr_no_instruction_stall);

    assign tr_instruction_issued_dec = instruction_issued;
    assign tr_instruction_pc_dec = ib.data_out.pc;
    assign tr_instruction_data_dec = ib.data_out.instruction;


endmodule
