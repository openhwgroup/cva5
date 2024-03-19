/*
 * Copyright © 2023 Chris Keilbart, Lesley Shannon
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module carry_save_shift

    import fpu_types::*;

    #(
        parameter WIDTH = 32 //Includes the integer bit
    )(
        input logic[WIDTH-1:0] four_wsum, //Shifted twice by the CALLER (because of special initialization)
        input logic[WIDTH-3:0] wcarry,
        input logic[WIDTH-4:0] divisor,

        output logic[WIDTH-3:0] next_wsum,
        output logic[WIDTH-3:0] next_wcarry,
        output q_t next_q,
        output logic not_in_table //Only used for assertion
    );

    logic[WIDTH-1:0] four_wcarry;
    assign four_wcarry = {wcarry, 1'b0, (next_q == POS_ONE || next_q == POS_TWO)}; //Include the carry in from converting -qd to 2s complement here

    logic[WIDTH-3:0] neg_q_d;
    always_comb begin
        if (next_q == POS_TWO || next_q == NEG_TWO)
            neg_q_d = {divisor, 1'b0};
        else if (next_q == ZERO)
            neg_q_d = '0;
        else
            neg_q_d = {1'b0, divisor};
        
        if (next_q == POS_ONE || next_q == POS_TWO)
            neg_q_d = ~neg_q_d;
    end

    q_lookup lut (
        .d(divisor[WIDTH-5 -: 3]),
        .ws(four_wsum[WIDTH-1 -: 7]),
        .wc(four_wcarry[WIDTH-1 -: 7]),
        .q(next_q),
        .not_in_table(not_in_table)
    );

    generate for (genvar i = 0; i < WIDTH-3; i++) begin : gen_carry_save_adder
        assign {next_wcarry[i+1], next_wsum[i]} = four_wsum[i] + four_wcarry[i] + neg_q_d[i];
    end endgenerate

    //Last adder - ignore the carry out
    assign next_wsum[WIDTH-3] = four_wsum[WIDTH-3] + four_wcarry[WIDTH-3] + neg_q_d[WIDTH-3];

    assign next_wcarry[0] = 0;

endmodule
