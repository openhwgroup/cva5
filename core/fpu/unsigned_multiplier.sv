/*
 * Copyright © 2019-2023 Yuhui Gao, Lesley Shannon
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
 *             Yuhui Gao <yuhuig@sfu.ca>
 */

module unsigned_multiplier 
#(
    parameter WIDTH = 53
)(
    input logic clk,
    input logic rst,
    input logic advance1,
    input logic advance2,
    input logic [WIDTH-1:0] rs1,
    input logic [WIDTH-1:0] rs2,
    output logic [2*WIDTH-1:0] out
);

    logic [WIDTH-1:0] rs1_r, rs2_r;

    always_ff @ (posedge clk) begin
        if (advance1) begin
            rs1_r <= rs1;
            rs2_r <= rs2;
        end

        if (advance2) begin
            out <= rs1_r * rs2_r;
        end
    end

endmodule
