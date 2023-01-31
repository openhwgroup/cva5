/*
 * Copyright © 2017-2020 Eric Matthews,  Lesley Shannon
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

module alu_unit

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    import opcodes::*;

    (
        input logic clk,
        input logic rst,

        input decode_packet_t decode_stage,
        output unit_needed,
        output logic [REGFILE_READ_PORTS-1:0] uses_rs,
        output logic uses_rd,
        
        input issue_packet_t issue_stage,
        input logic issue_stage_ready,
        input logic [31:0] constant_alu,
        input rs_addr_t issue_rs_addr [REGFILE_READ_PORTS],
        input logic [31:0] rf [REGFILE_READ_PORTS],

        unit_issue_interface.unit issue,
        unit_writeback_interface.unit wb
    );
    common_instruction_t instruction;//rs1_addr, rs2_addr, fn3, fn7, rd_addr, upper/lower opcode

    logic [31:0] alu_rs2_data;
    logic [32:0] alu_data1;
    logic [32:0] alu_data2;
    logic imm_type;
    alu_op_t alu_op;
    alu_op_t alu_op_r;
    logic subtract;

    logic[XLEN:0] add_sub_result;
    logic add_sub_carry_in;
    logic[XLEN:0] adder_in1;
    logic[XLEN:0] adder_in2;
    logic[XLEN-1:0] shift_result;
    logic[XLEN-1:0] result;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Decode
    assign instruction = decode_stage.instruction;

    assign unit_needed = decode_stage.instruction inside {
        LUI, AUIPC, JAL, JALR,
        ADDI, SLLI, SLTI, SLTIU, XORI, SRLI, SRAI, ORI, ANDI,
        ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND
    };
    always_comb begin
        uses_rs = '0;
        uses_rs[RS1] = decode_stage.instruction inside {
            JALR,
            ADDI, SLLI, SLTI, SLTIU, XORI, SRLI, SRAI, ORI, ANDI,
            ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND
        };
        uses_rs[RS2] = decode_stage.instruction inside {
            ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND
        };
        uses_rd = decode_stage.instruction inside {
            LUI, AUIPC, JAL, JALR,
            ADDI, SLLI, SLTI, SLTIU, XORI, SRLI, SRAI, ORI, ANDI,
            ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND
        };
    end

    always_comb begin
        case (instruction.upper_opcode) inside
            LUI_T, AUIPC_T, JAL_T, JALR_T : alu_op = ALU_CONSTANT;
            default : 
            case (instruction.fn3) inside
                SLTU_fn3, SLT_fn3 : alu_op = ALU_SLT;
                SLL_fn3, SRA_fn3 : alu_op = ALU_SHIFT;
                default : alu_op = ALU_ADD_SUB;
            endcase
        endcase
    end


    //Constant ALU:
    //  provides LUI, AUIPC, JAL, JALR results for ALU
    //  provides PC+4 for BRANCH unit and ifence in GC unit
    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            imm_type <= instruction.upper_opcode inside {ARITH_IMM_T};
            alu_op_r <= alu_op;
            subtract <= decode_stage.instruction inside {SUB, SLTI, SLTIU, SLT, SLTU};
        end
    end

    //logic and adder
    assign alu_data1 = {(rf[RS1][31] & ~issue_stage.fn3[0]), rf[RS1]};//(fn3[0]  is SLTU_fn3);
    assign alu_rs2_data = imm_type ? 32'(signed'(issue_stage.instruction[31:20])) : rf[RS2];
    assign alu_data2 = {(alu_rs2_data[31] & ~issue_stage.fn3[0]), alu_rs2_data};

    ////////////////////////////////////////////////////
    //Issue
    //Logic ops put through the adder carry chain to reduce resources
    always_comb begin
        case (issue_stage.fn3)
            XOR_fn3 : adder_in1 = alu_data1 ^ alu_data2;
            OR_fn3 : adder_in1 = alu_data1 | alu_data2;
            AND_fn3 : adder_in1 = alu_data1 & alu_data2;
            default : adder_in1 = alu_data1; //ADD/SUB/SLT/SLTU
        endcase
        case (issue_stage.fn3)
            XOR_fn3,
            OR_fn3,
            AND_fn3 : adder_in2 = 0;
            default : adder_in2 = alu_data2 ^ {33{subtract}};
        endcase
    end

    //Add/Sub ops
    assign {add_sub_result, add_sub_carry_in} = {adder_in1, 1'b1} + {adder_in2, subtract};
    
    //Shift ops
    barrel_shifter shifter (
        .shifter_input(rf[RS1]),
        .shift_amount(imm_type ? issue_rs_addr[RS2] : rf[RS2][4:0]),
        .arith(rf[RS1][31] & issue_stage.instruction[30]),
        .lshift(~issue_stage.fn3[2]),
        .shifted_result(shift_result)
    );

    always_comb begin
        case (alu_op_r)
            ALU_CONSTANT : result = constant_alu;//LUI, AUIPC, JAL, JALR
            ALU_ADD_SUB : result = add_sub_result[31:0];
            ALU_SLT : result = {31'b0, add_sub_result[32]};
            default : result = shift_result; //ALU_SHIFT
        endcase
    end

    ////////////////////////////////////////////////////
    //Output
    assign issue.ready = 1;
    assign wb.rd = result;
    assign wb.done = issue.possible_issue;
    assign wb.id = issue.id;
    assign wb.phys_addr = issue.phys_addr;

    ////////////////////////////////////////////////////
    //Assertions

endmodule
