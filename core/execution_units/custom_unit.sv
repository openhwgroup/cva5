/*
 * Copyright © 2022 Eric Matthews
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

module custom_unit

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
    logic [31:0] result;
    logic done;
    id_t id;
    ////////////////////////////////////////////////////
    //Implementation
    //Simple 2-cycle adder that adds rs1 and rs2
    //that has a throughput of 1 (so long as the result is accepted by the writeback stage)

    ////////////////////////////////////////////////////
    //Decode
    assign instruction = decode_stage.instruction;

    //The following signals should be asserted when the decoded instruction
    //is handled by this execution unit.
    assign unit_needed = decode_stage.instruction inside {CUSTOM};
    always_comb begin
        uses_rs = '0;
        uses_rs[RS1] = decode_stage.instruction inside {CUSTOM};
        uses_rs[RS2] = decode_stage.instruction inside {CUSTOM};
        uses_rd = decode_stage.instruction inside {CUSTOM};
    end
    ////////////////////////////////////////////////////
    //Issue
    assign issue.ready = ~wb.done;

    always_ff @(posedge clk) begin
        if (issue.new_request)
            id <=  issue.id;
    end

    always_ff @(posedge clk) begin
        if (issue.new_request)
           result <= rf[RS1] + rf[RS2];
    end

    ////////////////////////////////////////////////////
    //Write-back
    assign wb.rd = result;

    always_ff @ (posedge clk) begin
        if (rst)
            wb.done <= 0;
        else
            wb.done <= (wb.done & ~wb.ack) | issue.new_request;
    end
    assign wb.id = id;
endmodule
