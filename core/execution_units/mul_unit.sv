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

module mul_unit

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    import opcodes::*;

    (
        input logic clk,
        input logic rst,

        input decode_packet_t decode_stage,
        output logic unit_needed,
        output logic [REGFILE_READ_PORTS-1:0] uses_rs,
        output logic uses_rd,

        input issue_packet_t issue_stage,
        input logic issue_stage_ready,
        input logic [31:0] rf [REGFILE_READ_PORTS],

        unit_issue_interface.unit issue,
        unit_writeback_interface.unit wb
    );
    common_instruction_t instruction;//rs1_addr, rs2_addr, fn3, fn7, rd_addr, upper/lower opcode
    
    logic signed [63:0] result;
    logic mulh [2];
    logic valid [2];
    id_t id [2];

    logic rs1_is_signed, rs2_is_signed, is_mulhx;
    logic signed [32:0] rs1_ext, rs2_ext;
    logic signed [32:0] rs1_r, rs2_r;

    logic stage1_advance;
    logic stage2_advance;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Decode
    assign unit_needed = decode_stage.instruction inside {MUL, MULH, MULHSU, MULHU};
    always_comb begin
        uses_rs = '0;
        uses_rs[RS1] = unit_needed;
        uses_rs[RS2] = unit_needed;
        uses_rd = unit_needed;
    end

    assign instruction = decode_stage.instruction;
    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            rs1_is_signed <= instruction.fn3[1:0] inside {MULH_fn3[1:0], MULHSU_fn3[1:0]};
            rs2_is_signed <= instruction.fn3[1:0] inside {MULH_fn3[1:0]};
            is_mulhx <= instruction.fn3[1:0] inside {MULH_fn3[1:0], MULHSU_fn3[1:0], MULHU_fn3[1:0]};
        end
    end
    ////////////////////////////////////////////////////
    //Issue
    assign rs1_ext = signed'({rs1_is_signed & rf[RS1][31], rf[RS1]});
    assign rs2_ext = signed'({rs2_is_signed & rf[RS2][31], rf[RS2]});

    //Pipeline advancement control signals
    assign issue.ready = stage1_advance;
    assign stage1_advance = ~valid[0] | stage2_advance;
    assign stage2_advance = ~valid[1] | wb.ack;

    //Input and output registered Multiply
    always_ff @ (posedge clk) begin
        if (stage1_advance) begin
            rs1_r <= rs1_ext;
            rs2_r <= rs2_ext;
        end
        if (stage2_advance) begin
            result <= 64'(rs1_r * rs2_r);
        end
    end

    //Attribute Pipeline
    always_ff @ (posedge clk) begin
        if (stage1_advance) begin
            mulh[0] <= is_mulhx;
            id[0] <= issue.id;
        end
        if (stage2_advance) begin
            mulh[1] <= mulh[0];
            id[1] <= id[0];
        end
    end

    //Valid/Done Pipeline
    always_ff @ (posedge clk) begin
        if (rst)
            valid <= '{default: 0};
        else begin
            valid[0] <= stage1_advance ? issue.new_request : valid[0];
            valid[1] <= stage2_advance ? valid[0] : valid[1];
        end
    end

    //WB interface
    ////////////////////////////////////////////////////
    assign wb.rd = mulh[1] ? result[63:32] : result[31:0];
    assign wb.done = valid[1];
    assign wb.id = id[1];

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
