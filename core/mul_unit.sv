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
import riscv_types::*;
import taiga_types::*;

module mul_unit(
        input logic clk,
        input logic rst,

        input mul_inputs_t mul_inputs,
        unit_issue_interface.unit issue,
        unit_writeback_interface.unit wb
        );

    logic signed [63:0] result;
    logic mulh [2];
    logic done [2];
    id_t id [2];

    logic rs1_signed, rs2_signed;
    logic signed [32:0] rs1_ext, rs2_ext;
    logic signed [32:0] rs1_r, rs2_r;

    logic stage1_advance;
    logic stage2_advance;
    ////////////////////////////////////////////////////
    //Implementation
    assign rs1_signed = mul_inputs.op[1:0] inside {MULH_fn3[1:0], MULHSU_fn3[1:0]};//MUL doesn't matter
    assign rs2_signed = mul_inputs.op[1:0] inside {MUL_fn3[1:0], MULH_fn3[1:0]};//MUL doesn't matter

    assign rs1_ext = signed'({mul_inputs.rs1[31] & rs1_signed, mul_inputs.rs1});
    assign rs2_ext = signed'({mul_inputs.rs2[31] & rs2_signed, mul_inputs.rs2});

    assign issue.ready = (~done[0] | ~done[1]);//stage1_advance;
    assign stage1_advance = ~done[0] | stage2_advance;
    assign stage2_advance = ~done[1] | wb.ack;

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

    always_ff @ (posedge clk) begin
        if (stage1_advance) begin
            mulh[0] <= (mul_inputs.op[1:0] != MUL_fn3[1:0]);
            id[0] <= issue.id;
            done[0] <= issue.new_request;
        end
        if (stage2_advance) begin
            mulh[1] <= mulh[0];
            id[1] <= id[0];
            done[1] <= done[0];
        end
    end

    //Issue/write-back handshaking
    ////////////////////////////////////////////////////
    assign wb.rd = mulh[1] ? result[63:32] : result[31:0];
    assign wb.done = done[1];
    assign wb.id = id[1];
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
