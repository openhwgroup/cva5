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
import taiga_types::*;

module pre_decode
        (
        input logic clk,
        input logic rst,

        //Fetch
        input logic [31:0] pre_decode_instruction,
        input logic [31:0] pre_decode_pc,
        input branch_predictor_metadata_t branch_metadata,
        input logic branch_prediction_used,
        input logic [BRANCH_PREDICTOR_WAYS-1:0] bp_update_way,
        input logic pre_decode_push,

        //Global Control
        input logic gc_fetch_flush,

        //Decode
        input logic pre_decode_pop,
        output logic fb_valid,
        output fetch_buffer_packet_t fb
        );

    logic buffer_reset;

    logic [6:0] opcode;
    logic [4:0] opcode_trimmed;
    logic [4:0] rs1_addr;
    logic [4:0] rs2_addr;
    logic [4:0] rd_addr;
    logic [2:0] fn3;

    logic csr_imm_op;
    logic sys_op;

    logic rs1_link, rd_link, rs1_eq_rd, use_ras;

    logic push_to_reg;

    fetch_buffer_packet_t data_in;
    fetch_buffer_packet_t data_out;
    fifo_interface #(.DATA_WIDTH($bits(fetch_buffer_packet_t))) fb_fifo();

    ////////////////////////////////////////////////////
    //implementation
    //FIFO
    assign buffer_reset = rst | gc_fetch_flush;
    assign fb_fifo.supress_push = 0;//Covered by reseting on gc_fetch_flush

    assign fb_fifo.push = pre_decode_push & ((fb_valid & ~pre_decode_pop) | fb_fifo.valid);
    assign fb_fifo.pop = pre_decode_pop & fb_fifo.valid;
    assign fb_fifo.data_in = data_in;
    assign data_out = fb_fifo.data_out;

    assign push_to_reg = pre_decode_push &
    ((~fb_fifo.valid & fb_valid & pre_decode_pop) | (~fb_fifo.valid & ~fb_valid));


    //Bypass overrides
    always_ff @ (posedge clk) begin
        if (push_to_reg)
            fb <= data_in;
        else if (pre_decode_pop)
            fb <= data_out;
    end

    always_ff @ (posedge clk) begin
        if (buffer_reset)
            fb_valid <= 0;
        else if (pre_decode_push)
            fb_valid <= 1;
        else if (pre_decode_pop & ~fb_fifo.valid)
            fb_valid <= 0;
    end

    taiga_fifo #(
            .DATA_WIDTH($bits(fetch_buffer_packet_t)),
            .FIFO_DEPTH(FETCH_BUFFER_DEPTH)
        ) fb_fifo_block (.fifo(fb_fifo), .rst(buffer_reset), .*);

    ////////////////////////////////////////////////////
    //Pre-Decode
    assign data_in.instruction = pre_decode_instruction;
    assign data_in.pc = pre_decode_pc;

    //Instruction components
    assign fn3 = pre_decode_instruction[14:12];
    assign opcode = pre_decode_instruction[6:0];
    assign opcode_trimmed = opcode[6:2];

    assign rs1_addr = pre_decode_instruction[19:15];
    assign rs2_addr = pre_decode_instruction[24:20];
    assign rd_addr  = pre_decode_instruction[11:7];

    assign csr_imm_op = (opcode_trimmed == SYSTEM_T) && fn3[2];
    assign sys_op =  (opcode_trimmed == SYSTEM_T) && (fn3 == 0);


    ////////////////////////////////////////////////////
    //RAS Support
    assign rs1_link = (rs1_addr inside {1,5});
    assign rd_link = (rd_addr inside {1,5});
    assign rs1_eq_rd = (rs1_addr == rd_addr);
    assign use_ras =  (opcode_trimmed == JALR_T) && ((rs1_link & ~rd_link) | (rs1_link & rd_link & ~rs1_eq_rd));
    assign data_in.is_return = use_ras;
    assign data_in.is_call = (opcode_trimmed inside {JAL_T, JALR_T}) && rd_link;

    ////////////////////////////////////////////////////
    //Register File Support
    assign data_in.uses_rs1 = !(opcode_trimmed inside {LUI_T, AUIPC_T, JAL_T, FENCE_T} || csr_imm_op || sys_op);
    assign data_in.uses_rs2 = opcode_trimmed inside {BRANCH_T, STORE_T, ARITH_T, AMO_T};
    assign data_in.uses_rd = !(opcode_trimmed inside {BRANCH_T, STORE_T, FENCE_T} || sys_op);

    ////////////////////////////////////////////////////
    //Branch Predictor support
    assign data_in.branch_metadata = branch_metadata;
    assign data_in.branch_prediction_used = branch_prediction_used;
    assign data_in.bp_update_way = bp_update_way;

    ////////////////////////////////////////////////////
    //ALU Control Signals
    //Add cases: JAL, JALR, LUI, AUIPC, ADD[I], all logic ops
    //sub cases: SUB, SLT[U][I]
    logic sub_instruction;
    assign sub_instruction = (fn3 == ADD_SUB_fn3) && pre_decode_instruction[30] && opcode[5];//If ARITH instruction
    assign data_in.alu_sub = ~opcode[2] & (fn3 inside {SLTU_fn3, SLT_fn3} || sub_instruction);//opcode[2] covers LUI,AUIPC,JAL,JALR

        always_comb begin
        case (fn3)
            SLT_fn3 : data_in.alu_logic_op = ALU_LOGIC_ADD;
            SLTU_fn3 : data_in.alu_logic_op = ALU_LOGIC_ADD;
            SLL_fn3 : data_in.alu_logic_op = ALU_LOGIC_ADD;
            XOR_fn3 : data_in.alu_logic_op = ALU_LOGIC_XOR;
            OR_fn3 : data_in.alu_logic_op = ALU_LOGIC_OR;
            AND_fn3 : data_in.alu_logic_op = ALU_LOGIC_AND;
            SRA_fn3 : data_in.alu_logic_op = ALU_LOGIC_ADD;
            ADD_SUB_fn3 : data_in.alu_logic_op = ALU_LOGIC_ADD;
        endcase
        //put LUI, AUIPC, JAL and JALR through adder path
        data_in.alu_logic_op = opcode[2] ? ALU_LOGIC_ADD : data_in.alu_logic_op;
    end

    always_comb begin
        case (fn3)
            SLT_fn3 : data_in.alu_op = ALU_SLT;
            SLTU_fn3 : data_in.alu_op = ALU_SLT;
            SLL_fn3 : data_in.alu_op = ALU_LSHIFT;
            XOR_fn3 : data_in.alu_op = ALU_ADD_SUB;
            OR_fn3 : data_in.alu_op = ALU_ADD_SUB;
            AND_fn3 : data_in.alu_op = ALU_ADD_SUB;
            SRA_fn3 : data_in.alu_op = ALU_RSHIFT;
            ADD_SUB_fn3 : data_in.alu_op = ALU_ADD_SUB;
        endcase
        //put LUI, AUIPC, JAL and JALR through adder path
        data_in.alu_op = opcode[2] ? ALU_ADD_SUB : data_in.alu_op;
    end

    logic non_mul_div_arith_op;
    assign non_mul_div_arith_op = ((opcode_trimmed == ARITH_T) && ~pre_decode_instruction[25]);//pre_decode_instruction[25] denotes multiply/divide instructions
    assign data_in.alu_request = non_mul_div_arith_op || (opcode_trimmed inside {ARITH_IMM_T, AUIPC_T, LUI_T, JAL_T, JALR_T});
   always_comb begin
        if (opcode_trimmed inside {ARITH_T, ARITH_IMM_T})
            data_in.alu_rs1_sel = ALU_RS1_RF;
        else if (opcode_trimmed inside {JAL_T, JALR_T, AUIPC_T})//AUIPC JAL JALR
            data_in.alu_rs1_sel = ALU_RS1_PC;
        else
            data_in.alu_rs1_sel = ALU_RS1_ZERO;//LUI
    end

    always_comb begin
        if (opcode_trimmed inside {LUI_T, AUIPC_T}) //LUI or AUIPC
            data_in.alu_rs2_sel = ALU_RS2_LUI_AUIPC;
        else if (opcode_trimmed == ARITH_IMM_T) //ARITH_IMM
            data_in.alu_rs2_sel = ALU_RS2_ARITH_IMM;
        else if (opcode_trimmed inside {JAL_T, JALR_T} ) //JAL JALR
            data_in.alu_rs2_sel = ALU_RS2_JAL_JALR;
        else
            data_in.alu_rs2_sel = ALU_RS2_RF;
    end

    ////////////////////////////////////////////////////
    //Assertions

endmodule
