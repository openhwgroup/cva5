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

module mul_unit(
        input logic clk,
        input logic rst,

        input mul_inputs_t mul_inputs,
        unit_issue_interface.unit issue,
        unit_writeback_interface.unit wb
        );

    logic signed [65:0] result;
    logic [1:0] mulh;
    instruction_id_one_hot_t id_one_hot_done [1:0];
    instruction_id_t id [1:0];

    logic rs1_signed, rs2_signed;
    logic signed [32:0] rs1_ext, rs2_ext;
    logic signed [32:0] rs1_r, rs2_r;

    logic [31:0] rd_bank [MAX_INFLIGHT_COUNT-1:0];
    ////////////////////////////////////////////////////
    //Implementation

    assign rs1_signed = mul_inputs.op[1:0] inside {MULH_fn3[1:0], MULHSU_fn3[1:0]};//MUL doesn't matter
    assign rs2_signed = mul_inputs.op[1:0] inside {MUL_fn3[1:0], MULH_fn3[1:0]};//MUL doesn't matter

    assign rs1_ext = signed'({mul_inputs.rs1[31] & rs1_signed, mul_inputs.rs1});
    assign rs2_ext = signed'({mul_inputs.rs2[31] & rs2_signed, mul_inputs.rs2});

    //Input and output registered Multiply
    always_ff @ (posedge clk) begin
        rs1_r <= rs1_ext;
        rs2_r <= rs2_ext;
        result <= rs1_r * rs2_r;
    end

    always_ff @ (posedge clk) begin
        mulh[0] <= (mul_inputs.op[1:0] != MUL_fn3[1:0]);
        mulh[1] <= mulh[0];

        id[0] <= issue.instruction_id;
        id[1] <= id[0];

        id_one_hot_done[0] <= issue.instruction_id_one_hot & {MAX_INFLIGHT_COUNT{issue.new_request}};
        id_one_hot_done[1] <= id_one_hot_done[0];
    end

    ////////////////////////////////////////////////////
    //Output bank
     always_ff @ (posedge clk) begin
         if (|id_one_hot_done[1])
             rd_bank[id[1]] <= mulh[1] ? result[63:32] : result[31:0];
     end

    //Issue/write-back handshaking
    ////////////////////////////////////////////////////
    assign issue.ready = 1;
    assign wb.rd = rd_bank[wb.writeback_instruction_id];
    assign wb.rs1_data = rd_bank[wb.writeback_rs1_id];
    assign wb.rs2_data = rd_bank[wb.writeback_rs2_id];
    assign wb.done_next_cycle = id_one_hot_done[1];

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
