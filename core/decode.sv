/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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
        csr_inputs_interface.decode csr_inputs,
        output mul_inputs_t mul_inputs,
        output  div_inputs_t div_inputs,

        func_unit_ex_interface.decode alu_ex,
        func_unit_ex_interface.decode ls_ex,
        func_unit_ex_interface.decode branch_ex,
        func_unit_ex_interface.decode csr_ex,
        func_unit_ex_interface.decode mul_ex,
        func_unit_ex_interface.decode div_ex,

        output instruction_issued_no_rd,
        input logic instruction_complete,

        output logic dec_advance,
        output logic [31:0] dec_pc,
        output logic illegal_instruction

        );

    logic [2:0] fn3;
    logic [6:0] opcode;
    logic [4:0] shamt;

    assign fn3 = ib.data_out.instruction[14:12];
    assign opcode = ib.data_out.instruction[6:0];
    assign shamt = ib.data_out.instruction[24:20];

    logic uses_rs1;
    logic uses_rs2;
    logic uses_rd;

    logic [4:0] rs1_addr;
    logic [4:0] rs2_addr;
    logic [4:0] future_rd_addr;

    logic issue_valid;
    logic store_issued_with_forwarding;
    logic load_store_operands_ready;
    logic operands_ready;

    logic csr_imm_op;
    logic sys_op;

    logic mult_div_op;

    logic branch_compare;

    logic [NUM_WB_UNITS-1:0] new_request;
    logic [NUM_WB_UNITS-1:0] issue;

    logic unit_available;
    logic advance;

    logic [XLEN-1:0] alu_rs1_data;
    logic [XLEN-1:0] alu_rs2_data;

    logic [1:0] alu_op;
    logic [2:0] alu_fn3;

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

    assign csr_imm_op = (opcode == SYSTEM) && fn3[2];
    assign sys_op =  (opcode == SYSTEM) && (fn3 == 0);

    assign uses_rs1 = ib.data_out.uses_rs1;
    assign uses_rs2 = ib.data_out.uses_rs2;
    assign uses_rd = ib.data_out.uses_rd;

    assign rs1_addr = ib.data_out.instruction[19:15];
    assign rs2_addr = ib.data_out.instruction[24:20];
    assign future_rd_addr = ib.data_out.instruction[11:7];

    //Register File interface inputs
    assign rf_decode.rs1_addr  =  rs1_addr;
    assign rf_decode.rs2_addr  =  rs2_addr;
    assign rf_decode.future_rd_addr  =  future_rd_addr;
    assign rf_decode.instruction_issued = advance & uses_rd;
    assign rf_decode.id = id_gen.issue_id;
    //Issue logic
    always_comb begin
        case (opcode)
            LUI : illegal_instruction = 1'b0;
            AUIPC : illegal_instruction = 1'b0;
            JAL : illegal_instruction = 1'b0;
            JALR : illegal_instruction = 1'b0;
            BRANCH : illegal_instruction = 1'b0;
            LOAD : illegal_instruction = 1'b0;
            STORE : illegal_instruction = 1'b0;
            ARITH_IMM : illegal_instruction = 1'b0;
            ARITH : begin
                if (!USE_MUL && !USE_DIV)
                    illegal_instruction = ib.data_out.instruction[25];
                else if (!USE_MUL && USE_DIV)
                    illegal_instruction = ib.data_out.instruction[25] & ~fn3[2];
                else if (!USE_MUL && !USE_DIV)
                    illegal_instruction = ib.data_out.instruction[25] & fn3[2];
                else
                    illegal_instruction = 1'b0;
            end
            FENCE : illegal_instruction = 1'b0;
            AMO : illegal_instruction = 1'b0;
            SYSTEM : illegal_instruction = 1'b0;
            default : illegal_instruction = 1'b1;
        endcase
    end

    one_hot_to_integer #(NUM_WB_UNITS) iq_id (.one_hot(new_request), .int_out(iq.data_in.unit_id));

    assign iq.data_in.rd_addr = future_rd_addr;
    assign iq.data_in.id = id_gen.issue_id;
    assign iq.new_issue = advance & uses_rd;

    assign id_gen.advance = advance & uses_rd;

    assign bt.dec_pc = ib.data_out.pc;

    assign issue_valid =  ib.valid & ((~uses_rd) | (uses_rd & id_gen.id_avaliable)) & ~flush; //~(|delay) &


    assign operands_ready =  !(
            (uses_rs1 && rf_decode.rs1_conflict) ||
            (uses_rs2 && rf_decode.rs2_conflict));

    assign load_store_forward =((opcode == STORE) && last_ls_request_was_load && (rs2_addr == load_rd));

    assign load_store_operands_ready =  !(
            (uses_rs1 && rf_decode.rs1_conflict) ||
            (uses_rs2 && rf_decode.rs2_conflict && ~load_store_forward));

    assign mult_div_op = (opcode == ARITH) && ib.data_out.instruction[25];
    assign branch_compare = (opcode == BRANCH);

    assign new_request[BRANCH_UNIT_ID] = ((opcode == BRANCH) || (opcode == JAL) || (opcode == JALR));
    assign new_request[ALU_UNIT_ID] =  (((opcode == ARITH)  && ~ib.data_out.instruction[25]) || (opcode== ARITH_IMM)  || (opcode == AUIPC) || (opcode == LUI));
    assign new_request[LS_UNIT_ID] = (opcode == LOAD || opcode == STORE || opcode == AMO);
    assign new_request[CSR_UNIT_ID] = (opcode == SYSTEM);
    generate if (USE_MUL)
            assign new_request[MUL_UNIT_ID] = mult_div_op & ~fn3[2] ;
        else
            assign new_request[MUL_UNIT_ID] = 0 ;
    endgenerate
    generate if (USE_DIV)
            assign new_request[DIV_UNIT_ID] =mult_div_op & fn3[2] ;
        else
            assign new_request[DIV_UNIT_ID] = 0 ;
    endgenerate

    assign issue[BRANCH_UNIT_ID] = issue_valid & operands_ready & new_request[BRANCH_UNIT_ID] & (branch_ex.ready | ~uses_rd);//| ~uses_rd
    assign issue[ALU_UNIT_ID] = issue_valid & operands_ready & new_request[ALU_UNIT_ID] & alu_ex.ready;
    assign issue[LS_UNIT_ID] = issue_valid & load_store_operands_ready & new_request[LS_UNIT_ID] & ls_ex.ready;
    assign issue[CSR_UNIT_ID] = issue_valid & operands_ready &  new_request[CSR_UNIT_ID] & csr_ex.ready ;
    assign issue[MUL_UNIT_ID] = issue_valid & operands_ready & new_request[MUL_UNIT_ID] & mul_ex.ready;
    assign issue[DIV_UNIT_ID] = issue_valid & operands_ready & new_request[DIV_UNIT_ID] & div_ex.ready;

    assign advance =  |issue;

    assign ib.pop = advance;
    assign dec_advance = advance;
    assign instruction_issued_no_rd = advance & ~uses_rd;

    //----------------------------------------------------------------------------------
    //ALU unit inputs
    //----------------------------------------------------------------------------------
    assign alu_ex.new_request_dec = issue[ALU_UNIT_ID];

    always_comb begin
        if ((opcode == AUIPC))
            alu_rs1_data = ib.data_out.pc;
        else if (opcode == LUI)
            alu_rs1_data = '0;
        else
            alu_rs1_data = rf_decode.rs1_data;
    end

    always_comb begin
        if ((opcode == AUIPC) || (opcode == LUI))
            alu_rs2_data = {ib.data_out.instruction[31:12], 12'b0};
        else if (opcode == ARITH_IMM)
            alu_rs2_data = 32'(signed'(ib.data_out.instruction[31:20]));
        else// ARITH instructions
            alu_rs2_data = rf_decode.rs2_data;
    end

    assign alu_fn3 = ((opcode == AUIPC) || (opcode == LUI)) ? ADD_SUB_fn3 : fn3; //put lui and auipc through adder path
    always_comb begin
        case (alu_fn3)
            SLT_fn3 : alu_op = ALU_SLT;
            SLTU_fn3 : alu_op = ALU_SLT;
            SLL_fn3 : alu_op = ALU_SHIFT;
            XOR_fn3 : alu_op = ALU_LOGIC;
            OR_fn3 : alu_op = ALU_LOGIC;
            AND_fn3 : alu_op = ALU_LOGIC;
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
    always_ff @(posedge clk) begin
        if (issue[ALU_UNIT_ID]) begin
            alu_inputs.in1 <= alu_rs1_data;
            alu_inputs.in2 <= alu_rs2_data;
            alu_inputs.fn3 <= fn3;
            alu_inputs.add <= ~((opcode == ARITH && ib.data_out.instruction[30]) || ((opcode == ARITH || opcode == ARITH_IMM) &&  (fn3 ==SLTU_fn3 || fn3 ==SLT_fn3)));//SUB instruction
            alu_inputs.arith <= alu_rs1_data[XLEN-1] & ib.data_out.instruction[30];//shift in bit
            alu_inputs.left_shift <= ~fn3[2];
            alu_inputs.shifter_in <= fn3[2] ? rf_decode.rs1_data : left_shift_in;
            alu_inputs.sltu <= fn3[0];//(fn3 ==SLTU_fn3);
            alu_inputs.op <= alu_op;
        end
    end
    //----------------------------------------------------------------------------------

    //----------------------------------------------------------------------------------
    //Load Store unit inputs
    //----------------------------------------------------------------------------------
    assign ls_ex.new_request_dec = issue[LS_UNIT_ID];

    assign ls_offset = 32'(signed'(opcode[5] ? {ib.data_out.instruction[31:25], ib.data_out.instruction[11:7]} : ib.data_out.instruction[31:20]));

    assign ls_inputs.virtual_address = rf_decode.rs1_data + ls_offset;//rf_decode.rs1_data;
    assign ls_inputs.rs2 = rf_decode.rs2_data;
    assign ls_inputs.pc = ib.data_out.pc;
    assign ls_inputs.fn3 = ls_inputs.is_amo ? LS_W_fn3 : fn3;
    //assign ls_inputs.imm = opcode[5] ? {ib.data_out.instruction[31:25], ib.data_out.instruction[11:7]} : ib.data_out.instruction[31:20];
    assign ls_inputs.amo = ib.data_out.instruction[31:27];
    assign ls_inputs.is_amo = (opcode == AMO);
    assign ls_inputs.load = (opcode == LOAD) || ((opcode == AMO) && (ls_inputs.amo != AMO_SC)); //LR and AMO_ops perform a read operation as well
    assign ls_inputs.store = (opcode == STORE);
    assign ls_inputs.load_store_forward =  (opcode == STORE) && rf_decode.rs2_conflict;
    assign ls_inputs.id = id_gen.issue_id;

    always_ff @(posedge clk) begin
        if (issue[LS_UNIT_ID])
            load_rd <= future_rd_addr;
    end

    always_ff @(posedge clk) begin
        if (rst)
            last_ls_request_was_load <= 0;
        else if (issue[LS_UNIT_ID])
            last_ls_request_was_load <=  ls_inputs.load;
        else if (advance && uses_rd && (load_rd == future_rd_addr))
            last_ls_request_was_load <=0;
    end

    //----------------------------------------------------------------------------------

    //----------------------------------------------------------------------------------
    //Branch unit inputs
    //----------------------------------------------------------------------------------
    assign branch_ex.new_request_dec = issue[BRANCH_UNIT_ID];
    assign branch_inputs.rs1 = rf_decode.rs1_data;
    assign branch_inputs.rs2 = rf_decode.rs2_data;
    assign branch_inputs.fn3 = fn3;
    assign branch_inputs.dec_pc = ib.data_out.pc;
    assign branch_inputs.use_signed = !((fn3 == BLTU_fn3) || (fn3 == BGEU_fn3));
    assign branch_inputs.rdx0 = ~uses_rd;//(future_rd_addr == 0); jal jalr x0
    assign branch_inputs.rs1_addr = rs1_addr;
    assign branch_inputs.rd_addr = future_rd_addr;
    assign branch_inputs.prediction = ib.data_out.prediction;

    assign branch_inputs.jal = opcode[3];//(opcode == JAL);
    assign branch_inputs.jalr = ~opcode[3] & opcode[2];//(opcode == JALR);
    assign branch_inputs.branch_compare = (opcode[3:2] == 0) ;//(opcode == BRANCH);
    assign branch_inputs.jal_imm = {ib.data_out.instruction[31], ib.data_out.instruction[19:12], ib.data_out.instruction[20], ib.data_out.instruction[30:21]};
    assign branch_inputs.jalr_imm = ib.data_out.instruction[31:20];
    assign branch_inputs.br_imm = {ib.data_out.instruction[31], ib.data_out.instruction[7], ib.data_out.instruction[30:25], ib.data_out.instruction[11:8]};
    //----------------------------------------------------------------------------------

    //----------------------------------------------------------------------------------
    //CSR unit inputs
    //----------------------------------------------------------------------------------
    assign csr_ex.new_request_dec = issue[CSR_UNIT_ID];
    always_ff @(posedge clk) begin
        if (issue[CSR_UNIT_ID]) begin
            csr_inputs.rs1 <= csr_imm_op ? {27'b0, rs1_addr} : rf_decode.rs1_data; //immediate mode or rs1_addr reg
            csr_inputs.csr_addr <= ib.data_out.instruction[31:20];
            csr_inputs.csr_op <= fn3;
        end
    end
    //----------------------------------------------------------------------------------


    //----------------------------------------------------------------------------------
    //Mul Div unit inputs
    //----------------------------------------------------------------------------------
    assign mul_ex.new_request_dec = issue[MUL_UNIT_ID];
    assign mul_inputs.rs1 = rf_decode.rs1_data;
    assign mul_inputs.rs2 = rf_decode.rs2_data;
    assign mul_inputs.op = fn3[1:0];

    //If a subsequent div request uses the same inputs then
    //don't rerun div operation
    always_ff @(posedge clk) begin
        if (issue[DIV_UNIT_ID]) begin
            prev_div_rs1_addr <= rs1_addr;
            prev_div_rs2_addr <= rs2_addr;
        end
    end

    always_ff @(posedge clk) begin
        if (rst)
            prev_div_result_valid <= 0;
        else if (issue[DIV_UNIT_ID] && !(rs1_addr == future_rd_addr || rs2_addr == future_rd_addr))
            prev_div_result_valid <=1;
        else if (advance && uses_rd && (prev_div_rs1_addr == future_rd_addr || prev_div_rs2_addr == future_rd_addr))
            prev_div_result_valid <=0;
    end

    assign div_ex.new_request_dec = issue[DIV_UNIT_ID];
    assign div_inputs.rs1 = rf_decode.rs1_data;
    assign div_inputs.rs2 = rf_decode.rs2_data;
    assign div_inputs.op = fn3[1:0];
    assign div_inputs.reuse_result = prev_div_result_valid && (prev_div_rs1_addr == rs1_addr) && (prev_div_rs2_addr == rs2_addr);
    assign div_inputs.div_zero = (rf_decode.rs2_data == 0);

    //----------------------------------------------------------------------------------
    always_ff @(posedge clk) begin
        if(rst) begin
            branch_ex.new_request <= 0;
            alu_ex.new_request <= 0;
            ls_ex.new_request <= 0;
            csr_ex.new_request <= 0;
            mul_ex.new_request <= 0;
            div_ex.new_request <= 0;
        end else begin
            branch_ex.new_request <= issue[BRANCH_UNIT_ID];
            alu_ex.new_request <= issue[ALU_UNIT_ID];
            ls_ex.new_request <= issue[LS_UNIT_ID];
            csr_ex.new_request <= issue[CSR_UNIT_ID];
            mul_ex.new_request <= issue[MUL_UNIT_ID];
            div_ex.new_request <= issue[DIV_UNIT_ID];
        end
    end

endmodule
