/*
 * Copyright © 2017, 2018 Eric Matthews,  Lesley Shannon
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

        input logic flush,

        branch_table_interface.decode bt,
        instruction_buffer_interface.decode ib,

        id_generator_interface.decode id_gen,

        register_file_decode_interface.decode rf_decode,
        inflight_queue_interface.decode iq,

        output alu_inputs_t alu_inputs,
        output load_store_inputs_t ls_inputs,
        output branch_inputs_t branch_inputs,
        output csr_inputs_t csr_inputs,
        output gc_inputs_t gc_inputs,
        output mul_inputs_t mul_inputs,
        output  div_inputs_t div_inputs,

        func_unit_ex_interface.decode alu_ex,
        func_unit_ex_interface.decode ls_ex,
        func_unit_ex_interface.decode branch_ex,
        func_unit_ex_interface.decode csr_ex,
        func_unit_ex_interface.decode gc_ex,
        func_unit_ex_interface.decode mul_ex,
        func_unit_ex_interface.decode div_ex,

        input logic gc_issue_hold,
        input logic gc_issue_flush,

        output instruction_issued_no_rd,
        input logic instruction_complete,

        output logic dec_advance,
        output logic [31:0] dec_pc,
        output logic [31:0] dec_instruction,
        output logic illegal_instruction

        );

    logic [2:0] fn3;
    logic [6:0] opcode;
    logic [4:0] opcode_trim;

    logic [4:0] shamt;

    assign fn3 = ib.data_out.instruction[14:12];
    assign opcode = ib.data_out.instruction[6:0];
    assign opcode_trim = opcode[6:2];
    assign shamt = ib.data_out.instruction[24:20];

    logic uses_rs1;
    logic uses_rs2;
    logic uses_rd;

    logic [4:0] rs1_addr;
    logic [4:0] rs2_addr;
    logic [4:0] future_rd_addr;

    logic nop;

    logic issue_valid;
    logic store_issued_with_forwarding;
    logic load_store_operands_ready;
    logic operands_ready;

    logic csr_imm_op;
    logic sys_op;

    logic mult_div_op;

    logic [NUM_EX_UNITS-1:0] new_request;
    logic [NUM_EX_UNITS-1:0] issue_ready;
    logic [NUM_EX_UNITS-1:0] issue;

    logic advance;

    logic [XLEN-1:0] alu_rs1_data;
    logic [XLEN-1:0] alu_rs2_data;
    logic alu_sub;

    logic [1:0] alu_op;
    logic [1:0] alu_logic_op;

    logic [31:0] ls_offset;
    logic [31:0] virtual_address;

    logic [4:0] load_rd;
    logic last_ls_request_was_load;
    logic load_store_forward;

    logic [4:0] prev_div_rs1_addr;
    logic [4:0] prev_div_rs2_addr;
    logic prev_div_result_valid;
    //-----------------------------------------------------------------------------



    assign dec_pc =  ib.data_out.pc;
    assign dec_instruction = ib.data_out.instruction;

    assign csr_imm_op = (opcode_trim == SYSTEM_T) && fn3[2];
    assign sys_op =  (opcode_trim == SYSTEM_T) && (fn3 == 0);

    assign uses_rs1 = ib.data_out.uses_rs1;
    assign uses_rs2 = ib.data_out.uses_rs2;
    assign uses_rd = ib.data_out.uses_rd;

    assign rs1_addr = ib.data_out.instruction[19:15];
    assign rs2_addr = ib.data_out.instruction[24:20];
    assign future_rd_addr = ib.data_out.instruction[11:7];
    assign nop = (opcode_trim inside {LUI_T, AUIPC_T, ARITH_T, ARITH_IMM_T} && ib.data_out.rd_zero);

    //Register File interface inputs
    assign rf_decode.rs1_addr  =  rs1_addr;
    assign rf_decode.rs2_addr  =  rs2_addr;
    assign rf_decode.future_rd_addr  =  future_rd_addr;
    assign rf_decode.instruction_issued = advance & uses_rd & ~ib.data_out.rd_zero;
    assign rf_decode.id = id_gen.issue_id;
    //Issue logic

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

    one_hot_to_integer #(NUM_WB_UNITS) iq_id (.*, .one_hot(new_request[NUM_EX_UNITS-2:0]), .int_out(iq.data_in.unit_id));
    assign iq.data_in.id = id_gen.issue_id;
    assign iq.data_in.rd_addr = future_rd_addr;
    assign iq.data_in.rd_addr_nzero = ~ib.data_out.rd_zero;

    assign iq.new_issue = advance & uses_rd;

    assign id_gen.advance = advance & uses_rd;

    assign bt.dec_pc = ib.data_out.pc;

    assign issue_valid =  ib.valid & id_gen.id_avaliable & ~flush & ~gc_issue_hold & ~gc_issue_flush;


    assign operands_ready =  ~(
            (uses_rs1 & rf_decode.rs1_conflict) |
            (uses_rs2 & rf_decode.rs2_conflict));

    assign load_store_forward = ((opcode_trim == STORE_T) && last_ls_request_was_load && (rs2_addr == load_rd));

    assign load_store_operands_ready =  ~(
            (uses_rs1 & rf_decode.rs1_conflict) |
            (uses_rs2 & rf_decode.rs2_conflict & ~load_store_forward));

    assign mult_div_op = (opcode_trim == ARITH_T) && ib.data_out.instruction[25];

    assign new_request[BRANCH_UNIT_EX_ID] = opcode_trim inside {BRANCH_T, JAL_T, JALR_T} ? 1 : 0;
    assign new_request[ALU_UNIT_EX_ID] =  ((opcode_trim == ARITH_T)  && ~ib.data_out.instruction[25]) || opcode_trim inside {ARITH_IMM_T, AUIPC_T, LUI_T};
    assign new_request[LS_UNIT_EX_ID] = opcode_trim inside {LOAD_T, STORE_T, AMO_T} ? 1 : 0;
    assign new_request[CSR_UNIT_EX_ID] = (opcode_trim == SYSTEM_T) && (fn3 != 0);
    assign new_request[GC_UNIT_EX_ID] = ((opcode_trim == SYSTEM_T) && (fn3 == 0)) || (opcode_trim == FENCE_T);

    generate if (USE_MUL)
            assign new_request[MUL_UNIT_EX_ID] = mult_div_op & ~fn3[2];
    endgenerate
    generate if (USE_DIV)
            assign new_request[DIV_UNIT_EX_ID] = mult_div_op & fn3[2];
    endgenerate

    assign issue_ready[BRANCH_UNIT_EX_ID] = new_request[BRANCH_UNIT_EX_ID] & (branch_ex.ready | ~uses_rd);//| ~uses_rd
    assign issue_ready[ALU_UNIT_EX_ID] = new_request[ALU_UNIT_EX_ID] & alu_ex.ready;
    assign issue_ready[LS_UNIT_EX_ID] = new_request[LS_UNIT_EX_ID] & ls_ex.ready;
    assign issue_ready[CSR_UNIT_EX_ID] = new_request[CSR_UNIT_EX_ID] & csr_ex.ready;
    assign issue_ready[GC_UNIT_EX_ID] = new_request[GC_UNIT_EX_ID] & gc_ex.ready;
    generate if (USE_MUL)
            assign issue_ready[MUL_UNIT_EX_ID] = new_request[MUL_UNIT_EX_ID] & mul_ex.ready;
    endgenerate
    generate if (USE_DIV)
            assign issue_ready[DIV_UNIT_EX_ID] = new_request[DIV_UNIT_EX_ID] & div_ex.ready;
    endgenerate

    assign issue[BRANCH_UNIT_EX_ID] = issue_valid & operands_ready & issue_ready[BRANCH_UNIT_EX_ID];
    assign issue[ALU_UNIT_EX_ID] = issue_valid & operands_ready & issue_ready[ALU_UNIT_EX_ID];
    assign issue[LS_UNIT_EX_ID] = issue_valid & load_store_operands_ready & issue_ready[LS_UNIT_EX_ID];
    assign issue[CSR_UNIT_EX_ID] = issue_valid & operands_ready &  issue_ready[CSR_UNIT_EX_ID];
    assign issue[GC_UNIT_EX_ID] = issue_valid & operands_ready &  issue_ready[GC_UNIT_EX_ID];
    generate if (USE_MUL)
            assign issue[MUL_UNIT_EX_ID] = issue_valid & operands_ready & issue_ready[MUL_UNIT_EX_ID];
    endgenerate
    generate if (USE_DIV)
            assign issue[DIV_UNIT_EX_ID] = issue_valid & operands_ready & issue_ready[DIV_UNIT_EX_ID];
    endgenerate

    assign advance =  (|issue_ready) & issue_valid & load_store_operands_ready;

    assign ib.pop = advance;
    assign dec_advance = advance;
    assign instruction_issued_no_rd = advance & ~uses_rd;

    //----------------------------------------------------------------------------------
    //ALU unit inputs
    //----------------------------------------------------------------------------------
    assign alu_ex.new_request_dec = issue[ALU_UNIT_EX_ID];

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
            SLL_fn3 : alu_op = ALU_SHIFT;
            XOR_fn3 : alu_op = ALU_ADD_SUB;
            OR_fn3 : alu_op = ALU_ADD_SUB;
            AND_fn3 : alu_op = ALU_ADD_SUB;
            SRA_fn3 : alu_op = ALU_SHIFT;
            ADD_SUB_fn3 : alu_op = ALU_ADD_SUB;
        endcase
    end

    logic [XLEN-1:0] left_shift_in;
    //assign left_shift_in =  {<<{rf_decode.rs1_data}}; //Bit reverse not supported by Altera
    always_comb begin
        for (int i=0; i < XLEN; i=i+1) begin
            left_shift_in[i] = rf_decode.rs1_data[XLEN-i-1];
        end
    end

    //Add cases: LUI, AUIPC, ADD[I], all logic ops
    //sub cases: SUB, SLT[U][I]
    assign alu_sub = opcode[2] ? 0 : ((fn3 inside {SLTU_fn3, SLT_fn3}) || ((fn3 == ADD_SUB_fn3) && ib.data_out.instruction[30]) && opcode[5]);

    always_ff @(posedge clk) begin
        if (issue[ALU_UNIT_EX_ID]) begin
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
    //----------------------------------------------------------------------------------

    //----------------------------------------------------------------------------------
    //Load Store unit inputs
    //----------------------------------------------------------------------------------
    logic amo_op;
    logic [4:0] amo_type;
    assign amo_op =  USE_AMO ? (opcode_trim == AMO_T) : 0;
    assign amo_type = USE_AMO ? ib.data_out.instruction[31:27] : 0;

    assign ls_ex.new_request_dec = issue[LS_UNIT_EX_ID];

    assign ls_inputs.offset = opcode[5] ? {ib.data_out.instruction[31:25], ib.data_out.instruction[11:7]} : ib.data_out.instruction[31:20];
    assign ls_inputs.virtual_address = rf_decode.rs1_data;// + 32'(signed'(ls_inputs.offset));
    assign ls_inputs.rs2 = rf_decode.rs2_data;
    assign ls_inputs.pc = ib.data_out.pc;
    assign ls_inputs.fn3 = amo_op ? LS_W_fn3 : fn3;
    assign ls_inputs.amo = amo_type;
    assign ls_inputs.is_amo = amo_op;
    assign ls_inputs.load = (opcode_trim inside {LOAD_T, AMO_T}) && (amo_type != AMO_SC); //LR and AMO_ops perform a read operation as well
    assign ls_inputs.store = (opcode_trim == STORE_T);
    assign ls_inputs.load_store_forward = (opcode_trim == STORE_T) && rf_decode.rs2_conflict;
    assign ls_inputs.id = id_gen.issue_id;

    always_ff @(posedge clk) begin
        if (issue[LS_UNIT_EX_ID])
            load_rd <= future_rd_addr;
    end

    always_ff @(posedge clk) begin
        if (rst)
            last_ls_request_was_load <= 0;
        else if (advance) begin
            if (new_request[LS_UNIT_EX_ID] & ls_inputs.load)
                last_ls_request_was_load <= 1;
            else if (uses_rd && (load_rd == future_rd_addr))
                last_ls_request_was_load <=0;
        end
    end

    //----------------------------------------------------------------------------------

    //----------------------------------------------------------------------------------
    //Branch unit inputs
    //----------------------------------------------------------------------------------
    assign branch_ex.new_request_dec = issue[BRANCH_UNIT_EX_ID];
    assign branch_inputs.rs1 = rf_decode.rs1_data;
    assign branch_inputs.rs2 = rf_decode.rs2_data;
    assign branch_inputs.fn3 = fn3;
    assign branch_inputs.dec_pc = ib.data_out.pc;
    assign branch_inputs.use_signed = !(fn3 inside {BLTU_fn3, BGEU_fn3});
    assign branch_inputs.jal = opcode[3];//(opcode == JAL);
    assign branch_inputs.jalr = ~opcode[3] & opcode[2];//(opcode == JALR);
    assign branch_inputs.uses_rd = uses_rd;//not (future_rd_addr == 0); jal jalr x0
    assign branch_inputs.is_call = ib.data_out.is_call;
    assign branch_inputs.is_return = ib.data_out.is_return;
    assign branch_inputs.instruction = ib.data_out.instruction;
    //----------------------------------------------------------------------------------


    //----------------------------------------------------------------------------------
    //CSR unit inputs
    //----------------------------------------------------------------------------------
    assign csr_ex.new_request_dec = issue[CSR_UNIT_EX_ID];
    always_ff @(posedge clk) begin
        if (issue[CSR_UNIT_EX_ID]) begin
            csr_inputs.rs1 <= csr_imm_op ? {27'b0, rs1_addr} : rf_decode.rs1_data; //immediate mode or rs1_addr reg
            csr_inputs.csr_addr <= ib.data_out.instruction[31:20];
            csr_inputs.csr_op <= fn3[1:0];
            csr_inputs.rs1_is_zero <= (rs1_addr == 0);
            csr_inputs.rd_is_zero <= ib.data_out.rd_zero;
        end
    end
    //----------------------------------------------------------------------------------


    //----------------------------------------------------------------------------------
    //Mul Div unit inputs
    //----------------------------------------------------------------------------------
    generate if (USE_MUL) begin
            assign mul_ex.new_request_dec = issue[MUL_UNIT_EX_ID];
            assign mul_inputs.rs1 = rf_decode.rs1_data;
            assign mul_inputs.rs2 = rf_decode.rs2_data;
            assign mul_inputs.op = fn3[1:0];
        end
    endgenerate
    //If a subsequent div request uses the same inputs then
    //don't rerun div operation
    generate if (USE_DIV) begin
            always_ff @(posedge clk) begin
                if (issue[DIV_UNIT_EX_ID]) begin
                    prev_div_rs1_addr <= rs1_addr;
                    prev_div_rs2_addr <= rs2_addr;
                end
            end

            always_ff @(posedge clk) begin
                if (rst)
                    prev_div_result_valid <= 0;
                else if (advance) begin
                    if(new_request[DIV_UNIT_EX_ID] && !(future_rd_addr == rs1_addr ||  future_rd_addr == rs2_addr))
                        prev_div_result_valid <=1;
                    else if (uses_rd && (future_rd_addr == prev_div_rs1_addr || future_rd_addr == prev_div_rs2_addr))
                        prev_div_result_valid <=0;
                end
            end

            assign div_ex.new_request_dec = issue[DIV_UNIT_EX_ID];
            assign div_inputs.rs1 = rf_decode.rs1_data;
            assign div_inputs.rs2 = rf_decode.rs2_data;
            assign div_inputs.op = fn3[1:0];
            assign div_inputs.reuse_result = prev_div_result_valid && (prev_div_rs1_addr == rs1_addr) && (prev_div_rs2_addr == rs2_addr);
            assign div_inputs.div_zero = (rf_decode.rs2_data == 0);
        end
    endgenerate
    //----------------------------------------------------------------------------------
    always_ff @(posedge clk) begin
        branch_ex.new_request <= issue[BRANCH_UNIT_EX_ID];
        alu_ex.new_request <= issue[ALU_UNIT_EX_ID];
        ls_ex.new_request <= issue[LS_UNIT_EX_ID];
        csr_ex.new_request <= issue[CSR_UNIT_EX_ID];
        gc_ex.new_request <= issue[GC_UNIT_EX_ID];
    end

    generate if (USE_MUL)
            always_ff @(posedge clk) begin
                mul_ex.new_request <= issue[MUL_UNIT_EX_ID];
            end
        assign mul_ex.possible_issue = new_request[MUL_UNIT_EX_ID];
    endgenerate
    generate if (USE_DIV)
            always_ff @(posedge clk) begin
                div_ex.new_request <= issue[DIV_UNIT_EX_ID];
            end
        assign div_ex.possible_issue = new_request[DIV_UNIT_EX_ID];
    endgenerate

    assign branch_ex.possible_issue = new_request[BRANCH_UNIT_EX_ID];
    assign alu_ex.possible_issue = new_request[ALU_UNIT_EX_ID];
    assign ls_ex.possible_issue = new_request[LS_UNIT_EX_ID];
    assign csr_ex.possible_issue = new_request[CSR_UNIT_EX_ID];
    assign gc_ex.possible_issue = new_request[GC_UNIT_EX_ID];

endmodule
