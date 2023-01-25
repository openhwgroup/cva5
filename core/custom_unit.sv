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

    (
        input logic clk,
        input logic rst,
        unit_decode_interface.unit decode,
        unit_issue_interface.unit issue,
        input logic [31:0] rf [REGFILE_READ_PORTS],
        unit_writeback_interface.unit wb
    );

    logic [4:0] opcode_trim;
    logic [31:0] result;
    logic done;
    id_t id;
    phys_addr_t phys_addr;
    ////////////////////////////////////////////////////
    //Implementation
    //Simple 2-cycle adder that adds rs1 and rs2
    //that has a throughput of 1 (so long as the result is accepted by the writeback stage)

    ////////////////////////////////////////////////////
    //Decode
    assign opcode_trim = decode.instruction[6:2];

    //The following signals should be asserted when the decoded instruction
    //is handled by this execution unit.
    assign decode.unit_needed = opcode_trim inside {CUSTOM_T};
    assign decode.uses_rs[RS1] = decode.unit_needed;
    assign decode.uses_rs[RS2] = decode.unit_needed;
    assign decode.uses_rd = decode.unit_needed;

    ////////////////////////////////////////////////////
    //Issue
    assign issue.ready = ~wb.done;

    always_ff @(posedge clk) begin
        if (issue.new_request) begin
            id <=  issue.id;
            phys_addr <= issue.phys_addr;
        end
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
    assign wb.phys_addr = phys_addr;
endmodule
