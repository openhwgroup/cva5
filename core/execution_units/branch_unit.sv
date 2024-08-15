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

module branch_unit

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    import opcodes::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,

        input decode_packet_t decode_stage,
        output logic unit_needed,
        output logic [REGFILE_READ_PORTS-1:0] uses_rs,
        output logic uses_rd,
        
        input issue_packet_t issue_stage,
        input logic issue_stage_ready,
        input logic [31:0] constant_alu,
        input logic [31:0] rf [REGFILE_READ_PORTS],

        unit_issue_interface.unit issue,
        output branch_results_t br_results,
        output logic branch_flush,

        exception_interface.unit exception
    );
    common_instruction_t instruction;//rs1_addr, rs2_addr, fn3, fn7, rd_addr, upper/lower opcode

    logic branch_issued_r;
    logic result;

    //Branch Predictor
    logic branch_taken;
    logic branch_taken_ex;

    id_t id_ex;
    logic [31:0] jump_pc;
    logic [31:0] new_pc;
    logic [31:0] new_pc_ex;

    logic instruction_is_completing;

    logic branch_complete;
    logic jal_or_jalr_ex;

    logic [32:0] rs1;
    logic [32:0] rs2;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Decode
    assign instruction = decode_stage.instruction;

    assign unit_needed = decode_stage.instruction inside {
        BEQ, BNE, BLT, BGE, BLTU, BGEU, JALR, JAL
    };
    always_comb begin
        uses_rs = '0;
        uses_rs[RS1] = decode_stage.instruction inside {
            BEQ, BNE, BLT, BGE, BLTU, BGEU, JALR
        };
        uses_rs[RS2] = decode_stage.instruction inside {
            BEQ, BNE, BLT, BGE, BLTU, BGEU
        };
        uses_rd = 0;//JALR/JAL writeback handled by ALU
    end

    ////////////////////////////////////////////////////
    //RAS Support
    logic rs1_link;
    logic rd_link;
    logic rs1_eq_rd;
    logic is_return;
    logic is_call;

    assign rs1_link = instruction.rs1_addr inside {1,5};
    assign rd_link = instruction.rd_addr inside {1,5};
    assign rs1_eq_rd = (instruction.rs1_addr == instruction.rd_addr);

    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            is_return <= (instruction.upper_opcode inside {JALR_T}) & ((rs1_link & ~rd_link) | (rs1_link & rd_link & ~rs1_eq_rd));
            is_call <= (instruction.upper_opcode inside {JAL_T, JALR_T}) & rd_link;
        end
    end

    ////////////////////////////////////////////////////
    //PC Offset
    logic[19:0] jal_imm;
    logic[11:0] jalr_imm;
    logic[11:0] br_imm;

    logic [20:0] pc_offset;
    logic [20:0] pc_offset_r;
    assign jal_imm = {decode_stage.instruction[31], decode_stage.instruction[19:12], decode_stage.instruction[20], decode_stage.instruction[30:21]};
    assign jalr_imm = decode_stage.instruction[31:20];
    assign br_imm = {decode_stage.instruction[31], decode_stage.instruction[7], decode_stage.instruction[30:25], decode_stage.instruction[11:8]};

    always_comb begin
        case (decode_stage.instruction[3:2])
            2'b11 : pc_offset = 21'(signed'({jal_imm, 1'b0}));
            2'b01 : pc_offset = 21'(signed'(jalr_imm));
            default : pc_offset = 21'(signed'({br_imm, 1'b0}));
        endcase
    end
    always_ff @(posedge clk) begin
        if (issue_stage_ready)
            pc_offset_r <= pc_offset;
    end
    ////////////////////////////////////////////////////

    logic jalr;
    logic jal_or_jalr;
    logic br_use_signed;
    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            jalr <= (~decode_stage.instruction[3] & decode_stage.instruction[2]);
            jal_or_jalr <= decode_stage.instruction[2];
            br_use_signed <= !(instruction.fn3 inside {BLTU_fn3, BGEU_fn3});
        end
    end

    ////////////////////////////////////////////////////
    //Issue

    //Only stall condition is if the following instruction is not valid for pc comparisons.
    //If the next instruction isn't valid, no instruction can be issued anyways, so it
    //is safe to hardcode this to one.
    assign issue.ready = 1;

    //Branch new request is held if the following instruction hasn't arrived at decode/issue yet
    set_clr_reg_with_rst #(.SET_OVER_CLR(1), .WIDTH(1), .RST_VALUE(0)) branch_issued_m (
      .clk, .rst,
      .set(issue.new_request),
      .clr(issue_stage.stage_valid | exception.valid),
      .result(branch_issued_r)
    );

    //To determine if the branch was predicted correctly we need to wait until the
    //subsequent instruction has reached the issue stage
    assign instruction_is_completing = branch_issued_r & issue_stage.stage_valid;

    //Sign extend
    assign rs1 = {(rf[RS1][31] & br_use_signed), rf[RS1]};
    assign rs2 = {(rf[RS2][31] & br_use_signed), rf[RS2]};

    ////////////////////////////////////////////////////
    //Branch/Jump target determination
    //Branch comparison and final address calculation
    //are performed in the issue stage
    branch_comparator bc (
        .less_than(issue_stage.fn3[2]),
        .a(rs1),
        .b(rs2),
        .xor_result(issue_stage.fn3[0]),
        .result(result)
    );
    assign branch_taken = result | jal_or_jalr;

    assign jump_pc = (jalr ? rs1[31:0] : issue_stage.pc) + 32'(signed'(pc_offset_r));
    assign new_pc = branch_taken ? jump_pc : constant_alu;

    always_ff @(posedge clk) begin
        if (issue.new_request) begin
            branch_taken_ex <= branch_taken;
            new_pc_ex <= {new_pc[31:1], new_pc[0]  & ~jalr};
            id_ex <= issue.id;
            jal_or_jalr_ex <= jal_or_jalr;
        end
    end

    ////////////////////////////////////////////////////
    //Exception support
    generate if (CONFIG.MODES != BARE) begin : gen_branch_exception
        logic new_exception;

        assign new_exception = new_pc[1] & branch_taken & issue.new_request;
        always_ff @(posedge clk) begin
            if (rst)
                exception.valid <= 0;
            else
                exception.valid <= new_exception;
        end

        assign exception.possible = 0; //Not needed because branch_flush suppresses issue
        assign exception.code = INST_ADDR_MISSALIGNED;
        assign exception.tval = new_pc_ex;
        assign exception.pc = issue_stage.pc_r;
        assign exception.discard = 0;
    end
    endgenerate

    ////////////////////////////////////////////////////
    //Predictor support
    logic is_return_ex;
    logic is_call_ex;
    always_ff @(posedge clk) begin
        if (issue.possible_issue) begin
            is_return_ex <= is_return;
            is_call_ex <= is_call;
        end
    end

    assign br_results.id = id_ex;
    assign br_results.valid = instruction_is_completing;
    assign br_results.pc = issue_stage.pc_r;
    assign br_results.target_pc = new_pc_ex;
    assign br_results.branch_taken = branch_taken_ex;
    assign br_results.is_branch = ~jal_or_jalr_ex;
    assign br_results.is_return = is_return_ex;
    assign br_results.is_call = is_call_ex;

    assign branch_flush = instruction_is_completing & (issue_stage.pc[31:1] != new_pc_ex[31:1]);

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
