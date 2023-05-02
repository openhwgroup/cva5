/*
 * Copyright © 2019 Eric Matthews,  Lesley Shannon
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

module branch_comparator

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    (
        input logic less_than,
        input logic [32:0] a,
        input logic [32:0] b,
        input logic xor_result,
        output logic result
    );

    logic [31:0] eq_a;
    logic [31:0] eq_b;
    logic [31:0] ls_a;
    logic [31:0] ls_b;

    logic [15:0] sub_ls_a;
    logic [15:0] sub_ls_b;
    logic [15:0] sub_eq_a;

    logic [15:0] sub_toss;
    logic carry_out;

    logic eq_carry_in;
    logic ls_carry_in;
    logic carry_in;

    //implementation
    ////////////////////////////////////////////////////
    //Combines less than and equality comparison into the same carry chain logic
    //For equality: carry out from ab + ~a~b + 1 (sums pairs of zeros or ones)
    //For less than:carry out from  a +~b + 1
    ////////////////////////////////////////////////////
    assign eq_carry_in =
       ((a[0] & b[0]) | (~a[0] & ~b[0])) &
       ((a[1] & b[1]) | (~a[1] & ~b[1]));

    assign ls_carry_in =
        ((a[0] | ~b[0]) & (a[1] | ~b[1])) |
        (a[1] & ~b[1]);

    assign carry_in = less_than ? ls_carry_in : eq_carry_in;

    assign ls_a = {1'b0, a[32:2]};
    assign ls_b = {1'b1, ~b[32:2]};

    assign eq_a = {1'b0, a[32:2]} & {1'b0, b[32:2]};
    assign eq_b = {1'b0, ~a[32:2]} & {1'b0, ~b[32:2]};

    //Compressor
    //pairwise reduces carry generation
    always_comb begin
        foreach(sub_ls_a[i]) begin
            sub_ls_a[i] = ((ls_a[2*i] & ls_b[2*i]) & (ls_a[2*i + 1] | ls_b[2*i + 1])) | (ls_a[2*i + 1] & ls_b[2*i + 1]); //carry produced regardless of carry in
            sub_ls_b[i] = ((ls_a[2*i] & ls_b[2*i]) & (ls_a[2*i + 1] | ls_b[2*i + 1])) | (ls_a[2*i + 1] & ls_b[2*i + 1]) |
                ((ls_a[2*i] | ls_b[2*i]) & (ls_a[2*i + 1] | ls_b[2*i + 1])); // carry produced regardless of carry in OR carry produced if carry in

            sub_eq_a[i] = (eq_a[2*i] | eq_b[2*i]) & (eq_a[2*i + 1] | eq_b[2*i + 1]); //bits are equal
        end
        //branch_inputs.fn3[0] is xor_result and selects the inverse result
        //i.e. (not eq, greater than).  Included here to reduce the number of inputs
        //in the branch target adder
        sub_ls_a[15] ^= xor_result;
        sub_eq_a[15] ^= xor_result;
    end

    assign {result, sub_toss} = {less_than ? sub_ls_a : sub_eq_a, carry_in} + {less_than ? sub_ls_b : 16'b0, carry_in};

endmodule
