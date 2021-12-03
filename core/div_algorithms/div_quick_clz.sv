/*
 * Copyright © 2017-2020 Eric Matthews,  Lesley Shannon
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
               Alec Lu <alec_lu@sfu.ca>
 */


module div_quick_clz
    #(
        parameter DIV_WIDTH = 32
    )
    (
        input logic clk,
        input logic rst,
        unsigned_division_interface.divider div
    );

    logic running;
    logic terminate;
    logic [DIV_WIDTH-1:0] divisor_r;

    logic [DIV_WIDTH-1:0] normalized_divisor;

    logic overflow;
    logic [DIV_WIDTH-1:0] subtraction1;
    logic [DIV_WIDTH-1:0] subtraction2;

    logic [DIV_WIDTH-1:0] new_remainder;
    logic [DIV_WIDTH-1:0] new_quotient;

    logic [DIV_WIDTH-1:0] new_Q_bit1;
    logic [DIV_WIDTH-1:0] new_Q_bit2;

    logic [DIV_WIDTH-1:0] test_multiple1;
    logic [DIV_WIDTH-1:0] test_multiple2;

    localparam CLZ_W = $clog2(DIV_WIDTH);
    logic [CLZ_W-1:0] remainder_CLZ;
    logic [CLZ_W-1:0] divisor_CLZ;
    logic [CLZ_W-1:0] divisor_CLZ_r;
    logic [CLZ_W-1:0] CLZ_delta;
    logic divisor_is_zero_first_cycle;
    ////////////////////////////////////////////////////
    //Implementation
    clz remainder_clz_block (.clz_input(div.remainder), .clz(remainder_CLZ));
    clz divisor_clz_block (.clz_input(div.divisor), .clz(divisor_CLZ));

    ////////////////////////////////////////////////////
    //Control Signals
    assign divisor_is_zero_first_cycle = (&divisor_CLZ) & ~div.divisor[0];
    always @ (posedge clk) begin
        if (div.start)
            div.divisor_is_zero <= divisor_is_zero_first_cycle;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            running <= 0;
        else if (div.start & ~divisor_is_zero_first_cycle)
            running <= 1;
        else if (terminate)
            running <= 0;
    end

    always_ff @ (posedge clk) begin
        div.done <= (running & terminate) | (div.start & divisor_is_zero_first_cycle);
    end

    assign terminate = div.remainder < divisor_r;

    ////////////////////////////////////////////////////
    //Divisor Pre-processing
    always_ff @ (posedge clk) begin
        if (div.start) begin
            divisor_r <= div.divisor;
            divisor_CLZ_r <= divisor_CLZ;
            normalized_divisor <= div.divisor << divisor_CLZ;
        end
    end

    ////////////////////////////////////////////////////
    //Remainder Determination
    assign test_multiple1 = normalized_divisor >> remainder_CLZ;
    assign {overflow, subtraction1} = div.remainder - test_multiple1;

    assign test_multiple2 = test_multiple1 >> 1;
    assign subtraction2 = div.remainder - test_multiple2;

    assign new_remainder = overflow ? subtraction2 : subtraction1;

    initial begin
        div.remainder = 0;
    end
    always @ (posedge clk) begin
        if (div.start)
            div.remainder <= div.dividend;
        else if (~terminate & running)
            div.remainder <= new_remainder;
    end

    ////////////////////////////////////////////////////
    //Quotient Determination
    assign CLZ_delta = divisor_CLZ_r - remainder_CLZ;
    always_comb begin
        new_Q_bit1 = 0;
        new_Q_bit1[CLZ_delta] = 1;
    end
    assign new_Q_bit2 = new_Q_bit1 >> 1;
    assign new_quotient = div.quotient | (overflow ?  new_Q_bit2 : new_Q_bit1);

    always_ff @ (posedge clk) begin
        if (div.start)
            div.quotient <= '0;
        else if (~terminate & running)
            div.quotient <= new_quotient;
    end
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
endmodule
