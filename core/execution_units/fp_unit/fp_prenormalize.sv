/*
 * Copyright © 2019-2023 Yuhui Gao, Chris Keilbart, Lesley Shannon
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module fp_prenormalize

    import cva5_config::*;
    import fpu_types::*;

    (
        input logic single,
        input logic right_shift_in,
        input logic overflow_in,
        input logic subnormal,
        input expo_d_t expo_in,
        input logic ignore_max_expo,
        input fp_shift_amt_t left_shift_amt,
        input fp_shift_amt_t right_shift_amt,

        output logic right_shift_out,
        output logic dp_overflow_out,
        output logic sp_overflow_out,
        output fp_shift_amt_t shift_amt_out,
        output expo_d_t dp_expo_out,
        output expo_s_t sp_expo_out
    );

    logic[EXPO_WIDTH:0] starting_expo;
    assign starting_expo = {overflow_in, expo_in};

    ////////////////////////////////////////////////////
    //Double precision
    //Left shifts are capped at reducing the exponent to 0
    //Right shifts increment the exponent except when subnormal
    logic expo_less_than_left_shift_amt;
    fp_shift_amt_t left_shift_amt_adjusted;
    logic[EXPO_WIDTH:0] expo_norm_left_shift_intermediate;
    logic[EXPO_WIDTH:0] expo_norm_left_shift;
    logic[EXPO_WIDTH:0] expo_norm_right_shift;
    logic dp_overflow_intermediate;

    //Left shift logic - cap the left shift amount to the exponent if it would turn negative
    assign {expo_less_than_left_shift_amt, expo_norm_left_shift_intermediate} = {starting_expo & {(EXPO_WIDTH+1){~subnormal}}} - (EXPO_WIDTH+1)'(left_shift_amt); //drive to zero if subnormal
    assign left_shift_amt_adjusted = expo_less_than_left_shift_amt ? expo_in : left_shift_amt;
    assign expo_norm_left_shift = expo_less_than_left_shift_amt ? '0 : expo_norm_left_shift_intermediate;

    //Right shift logic - exponent is zero if subnormal
    assign expo_norm_right_shift = subnormal ? '0 : starting_expo + (EXPO_WIDTH+1)'(right_shift_amt);
    
    //Select the final double precision exponent and overflow value
    assign {dp_overflow_intermediate, dp_expo_out} = right_shift_in ? expo_norm_right_shift : expo_norm_left_shift;
    assign dp_overflow_out = dp_overflow_intermediate | (~ignore_max_expo & &dp_expo_out);

    ////////////////////////////////////////////////////
    //Single precision
    //Normal double numbers map onto the subnormal single range
    //This means left shifts may turn into right shifts
    logic[EXPO_WIDTH-1:0] single_shift_amt;
    logic[EXPO_WIDTH-1:0] expo_sum;
    logic shift_sign;

    always_comb begin
        single_shift_amt = right_shift_in ? right_shift_amt : -left_shift_amt;
        expo_sum = expo_in + single_shift_amt;
        sp_overflow_out = overflow_in | (expo_sum > BIAS+BIAS_F & ~&expo_sum); //All 1 = NaN/infinity but not an overflow
        
        //Determine SP expo and shift amount due to subnormal numbers
        sp_expo_out = '0;
        if (expo_sum <= BIAS-BIAS_F && expo_sum > BIAS-BIAS_F-FRAC_WIDTH_F-3)
            single_shift_amt += (BIAS-BIAS_F+1) - expo_sum;
        else if (expo_sum <= BIAS-BIAS_F-FRAC_WIDTH_F-3) //Cap shift amount to prevent losing the sticky bit entirely
            single_shift_amt += FRAC_WIDTH_F+3;
        else //Maps onto regular range
            sp_expo_out = {expo_sum[EXPO_WIDTH-1], expo_sum[EXPO_WIDTH_F-2:0]};
        
        shift_sign = single_shift_amt[EXPO_WIDTH-1];
        if (shift_sign)
            single_shift_amt = -single_shift_amt;
        
        if (single) begin
            right_shift_out = ~shift_sign;
            shift_amt_out = single_shift_amt;
        end
        else begin
            right_shift_out = right_shift_in;
            shift_amt_out = right_shift_in ? right_shift_amt : left_shift_amt_adjusted;
        end
    end

endmodule
