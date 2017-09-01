/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 * 
 * This Source Code Form is "Incompatible With Secondary Licenses", as
 * defined by the Mozilla Public License, v. 2.0.
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
