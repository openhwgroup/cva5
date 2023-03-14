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

module fp_prenormalize
    import taiga_config::*;
    import fpu_types::*;

(
    input logic single,
    input logic right_shift_in,
    input logic overflow_in,
    input logic subnormal,
    input logic hidden_bit,
    input logic[EXPO_WIDTH-1:0] expo_in,
    input logic[EXPO_WIDTH-1:0] left_shift_amt,
    input logic[EXPO_WIDTH-1:0] right_shift_amt,

    output logic right_shift_out,
    output logic dp_overflow_out,
    output logic sp_overflow_out,
    output logic[EXPO_WIDTH-1:0] shift_amt_out,
    output logic[EXPO_WIDTH-1:0] dp_expo_out,
    output logic[EXPO_WIDTH_F-1:0] sp_expo_out
);

    logic expo_less_than_left_shift_amt;
    logic[EXPO_WIDTH-1:0] left_shift_amt_adjusted;
    logic[EXPO_WIDTH:0] expo_norm_left_shift_intermediate;
    logic[EXPO_WIDTH:0] expo_norm_left_shift;

    assign {expo_less_than_left_shift_amt, expo_norm_left_shift_intermediate} = {{overflow_in, expo_in} & {(EXPO_WIDTH+1){~subnormal}}} - (EXPO_WIDTH+1)'(left_shift_amt); //drive to zero if subnormal
    assign left_shift_amt_adjusted = expo_less_than_left_shift_amt ? expo_in : left_shift_amt;
    assign expo_norm_left_shift = (expo_norm_left_shift_intermediate & {(EXPO_WIDTH+1){~expo_less_than_left_shift_amt}}) + (EXPO_WIDTH)'({subnormal&hidden_bit});


    logic[EXPO_WIDTH:0] expo_norm_right_shift;
    logic[EXPO_WIDTH:0] subnormal_expo, subnormal_right_shift_amt;

    assign subnormal_expo = {overflow_in, expo_in} & {(EXPO_WIDTH+1){~subnormal}};
    assign subnormal_right_shift_amt = (EXPO_WIDTH+1)'(right_shift_amt) & {(EXPO_WIDTH+1){~subnormal}};
    assign expo_norm_right_shift = subnormal_expo + subnormal_right_shift_amt;

    assign {dp_overflow_out, dp_expo_out} = right_shift_in ? expo_norm_right_shift : expo_norm_left_shift;

    logic[EXPO_WIDTH-1:0] shift_sum;
    logic[EXPO_WIDTH-1:0] expo_sum;
    logic shift_sign;
    always_comb begin
        shift_sum = right_shift_in ? right_shift_amt : -left_shift_amt;
        expo_sum = expo_in + shift_sum;
        sp_overflow_out = overflow_in | (expo_sum > BIAS+BIAS_F && ~&expo_sum);
        sp_expo_out = '0;
        if (expo_sum <= BIAS-BIAS_F && expo_sum > BIAS-BIAS_F-FRAC_WIDTH_F-3)
            shift_sum += (BIAS-BIAS_F+1) - expo_sum;
        else if (expo_sum <= BIAS-BIAS_F-FRAC_WIDTH_F-3) //Cap shift amount to prevent losing the sticky bit entirely
            shift_sum += FRAC_WIDTH_F+3;
        else
            sp_expo_out = {expo_sum[EXPO_WIDTH-1], expo_sum[EXPO_WIDTH_F-2:0]};
        shift_sign = shift_sum[EXPO_WIDTH-1];
        if (shift_sign)
            shift_sum = -shift_sum;
        
        if (single) begin
            shift_amt_out = shift_sum;
            right_shift_out = ~shift_sign;
        end
        else begin
            right_shift_out = right_shift_in;
            shift_amt_out = right_shift_in ? right_shift_amt : left_shift_amt_adjusted;
        end
    end

endmodule
