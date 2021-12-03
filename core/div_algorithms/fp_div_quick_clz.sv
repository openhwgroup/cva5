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
               Alec Lu <alec_lu@sfu.ca>
               Yuhui Gao <yuhuig@sfu.ca>
 */


module fp_div_quick_clz #(parameter PRECISION=54)
    //PRECISION is the number of bits to calculate in the fractional part of mantissa
    (
        input logic clk,
        input logic rst,
        unsigned_division_interface.divider div
    );

    logic running;
    logic terminate;
    logic [div.DATA_WIDTH-1:0] divisor_r;

    logic [div.DATA_WIDTH-1:0] normalized_divisor;

    logic overflow;
    logic [div.DATA_WIDTH-1:0] subtraction1;
    logic [div.DATA_WIDTH-1:0] subtraction2;

    logic [div.DATA_WIDTH-1:0] new_remainder;
    logic [div.DATA_WIDTH-1:0] new_quotient;

    logic [div.DATA_WIDTH-1:0] new_Q_bit1;
    logic [div.DATA_WIDTH-1:0] new_Q_bit2;

    logic [div.DATA_WIDTH-1:0] test_multiple1;
    logic [div.DATA_WIDTH-1:0] test_multiple2;

    localparam CLZ_W = $clog2(div.DATA_WIDTH);
    logic [CLZ_W-1:0] remainder_CLZ;
    logic [CLZ_W-1:0] divisor_CLZ;
    logic [CLZ_W-1:0] divisor_CLZ_r;
    logic [CLZ_W-1:0] CLZ_delta;
    int i;
    localparam DIVISOR_CLZ = PRECISION[CLZ_W-1:0];
    ////////////////////////////////////////////////////
    //Implementation
    //OPT: remainder_CLZ cannot be more than PRECISION 
    //otherwise would've terminated.  
    //OPT: precisions with FRAC_WIDTH+2 < 32 can use the clz submodule instead
    //of for loop
    always_comb begin
        for (i = 0; i < PRECISION; i++) begin 
            if (div.remainder[div.DATA_WIDTH-1-i] == 1) begin 
                break;
            end 
        end
        remainder_CLZ = i[CLZ_W-1:0];
    end

    //assuming inputs are always normalized
    assign divisor_CLZ = DIVISOR_CLZ;

    ////////////////////////////////////////////////////
    //Control Signals
    //assign div.divisor_is_zero = (&divisor_CLZ) & ~div.divisor[0];

    always_ff @ (posedge clk) begin
        if (rst)
            running <= 0;
        else if (div.start) //(div.start & ~div.divisor_is_zero)
            running <= 1;
        else if (terminate)
            running <= 0;
    end

    ////////////////////////////////////////////////////
    //Divisor Pre-processing
    always_ff @ (posedge clk) begin
        divisor_CLZ_r <= divisor_CLZ;
        normalized_divisor <= {div.divisor[0+:FRAC_WIDTH+1], {(PRECISION){1'b0}}};
        //if (div.start) begin
            //divisor_r <= div.divisor;
        //end
    end

    always_ff @ (posedge clk) begin
        div.done <= (running & terminate);// | (div.start & div.divisor_is_zero);
    end
    //assign div.done = running & terminate;

    assign terminate = div.remainder < div.divisor;

    ////////////////////////////////////////////////////
    //Remainder Determination
    assign test_multiple1 = normalized_divisor >> remainder_CLZ;
    assign {overflow, subtraction1} = div.remainder - test_multiple1;

    assign test_multiple2 = {1'b0, test_multiple1[div.DATA_WIDTH-1:1]};    //test_multiple1 >> 1;
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
