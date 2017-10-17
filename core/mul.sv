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
 
module mul
        #(
        parameter CYCLES = 4
        )
        (
        input logic clk,
        input logic new_request,
        input logic [1:0] op,
        output logic done,
        output logic [1:0] completed_op,
        input logic [31:0] A,
        input logic [31:0] B,
        output logic [63:0] P
        );

    logic [32:0] A_r;
    logic [32:0] B_r;
    logic [65:0] result [0:CYCLES-1];
    logic valid [0:CYCLES];
    logic[1:0] mul_type [0:CYCLES];

    logic unsigned_A_op;
    logic unsigned_B_op;


    assign unsigned_A_op = (op == 2'b11);
    assign unsigned_B_op =op[1];

    always_ff @ (posedge clk) begin
        A_r <= signed'({A[31] & ~unsigned_A_op, A});
        B_r <= signed'({B[31] & ~unsigned_B_op,B});
        valid[0] <= new_request;
        mul_type[0] <= op;
        valid[1] <= valid[0];
        mul_type[1] <= mul_type[0];

        result[0] <= signed'(A_r) * signed'(B_r);
        for (int i = 0; i < CYCLES-1; i = i+1) begin
            result[i+1] <= result[i];
            valid[i+2] <= valid[i+1];
            mul_type[i+2] <= mul_type[i+1];
        end

    end

    assign P = result[CYCLES-1][63:0];
    assign done = valid[CYCLES];
    assign completed_op = mul_type[CYCLES];
endmodule
