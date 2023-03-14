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

module fp_normalize
    import taiga_config::*;
    import fpu_types::*;

(
    //input logic [2:0] rm,
    input fp_normalize_packet_t fp_normalize_packet,
    output fp_normalize_pre_processing_packet_t fp_normalize_pre_processing_packet
);

    logic sign;
    logic [EXPO_WIDTH-1:0] expo ;
    logic expo_overflow;
    logic [FRAC_WIDTH-1:0] frac;
    fp_shift_amt_t left_shift_amt;
    logic subnormal;
    logic right_shift;
    logic [EXPO_WIDTH-1:0] right_shift_amt;
    logic hidden_bit;
    logic frac_safe_bit;
    logic frac_carry_bit;
    logic [EXPO_WIDTH-1:0] expo_norm;
    logic expo_overflow_norm;
    grs_t grs;

    logic [EXPO_WIDTH:0] expo_norm_right_shift, expo_norm_left_shift;// right_shift_amt;
    logic [EXPO_WIDTH:0] subnormal_expo, subnormal_right_shift_amt;
    logic [EXPO_WIDTH:0] normal_expo;
    logic [1:0] normal_right_shift_amt;

    logic expo_less_than_left_shift_amt;
    fp_shift_amt_t left_shift_amt_adjusted;
    logic [EXPO_WIDTH:0] expo_norm_left_shift_intermediate;

    logic signed [FRAC_WIDTH+3+GRS_WIDTH-1:0] left, right;

    ////////////////////////////////////////////////////
    //Unpack inputs
    assign sign            = fp_normalize_packet.data[FLEN-1];
    assign expo_overflow   = fp_normalize_packet.expo_overflow;
    assign expo            = fp_normalize_packet.data[FLEN-2-:EXPO_WIDTH];
    assign frac            = fp_normalize_packet.data[FRAC_WIDTH-1:0];
    assign left_shift_amt  = fp_normalize_packet.clz;
    assign subnormal       = fp_normalize_packet.subnormal;
    assign right_shift     = fp_normalize_packet.right_shift;
    assign right_shift_amt = fp_normalize_packet.right_shift_amt;
    assign hidden_bit      = fp_normalize_packet.hidden;
    assign frac_safe_bit   = fp_normalize_packet.safe;
    assign frac_carry_bit  = fp_normalize_packet.carry;
    assign grs             = fp_normalize_packet.grs;

    ////////////////////////////////////////////////////
    //Implementation
    //Expo_overflow: FMUL, FDIV can assert
    //Expo_overflow_norm: FADD, FMUL can assert due to right shifting

    //Right Shift
    //Needed by: FADD, FDIV, FMUL
    //The right shift amt is calculated by each unit; subnormal needs to support larger right shifter due to the multiplication's pre-normalization; normal's right shift amt cannot exceed 2
    generate if (ENABLE_SUBNORMAL) begin
        assign subnormal_expo = {expo_overflow, expo} & {(EXPO_WIDTH+1){~subnormal}};
        assign subnormal_right_shift_amt = (EXPO_WIDTH+1)'(right_shift_amt) & {(EXPO_WIDTH+1){~subnormal}};
        assign expo_norm_right_shift = subnormal_expo + subnormal_right_shift_amt;
    end else begin
        assign normal_expo = {expo_overflow, expo} & {(EXPO_WIDTH+1){~subnormal}}; //drive result expo to zero if subnormal
        assign normal_right_shift_amt = (right_shift_amt[1:0]) & {2{~subnormal}};
        assign expo_norm_right_shift = normal_expo + (EXPO_WIDTH+1)'(normal_right_shift_amt);
    end endgenerate

    //Left Shift
    //Neededby: FSUB; FSQRT if subnormal is enabled
    //Left shift is done by first reversing the bit order and sign-shifted(>>>)
    //This is needed to preserve the sticky bit
    generate if (ENABLE_SUBNORMAL) begin
        //FADD of two subnormals may result in promotion of subnormal to normal
        //This is handled by adding 1 to the expo if the hidden_bit is 1, and |expo==0
        assign {expo_less_than_left_shift_amt, expo_norm_left_shift_intermediate} = {{expo_overflow, expo} & {(EXPO_WIDTH+1){~subnormal}}} - (EXPO_WIDTH+1)'(left_shift_amt); //drive to zero if subnormal
        assign left_shift_amt_adjusted = expo_less_than_left_shift_amt ? expo : left_shift_amt;
        assign expo_norm_left_shift = (expo_norm_left_shift_intermediate & {(EXPO_WIDTH+1){~expo_less_than_left_shift_amt}}) + (EXPO_WIDTH)'({subnormal&hidden_bit});
    end else begin
        assign {expo_less_than_left_shift_amt, expo_norm_left_shift_intermediate} = {{expo_overflow, expo} & {(EXPO_WIDTH+1){~subnormal}}} - (EXPO_WIDTH+1)'(left_shift_amt); //drive to zero if subnormal
        assign left_shift_amt_adjusted = expo_less_than_left_shift_amt ? expo : left_shift_amt;
        assign expo_norm_left_shift = (expo_norm_left_shift_intermediate & {(EXPO_WIDTH+1){~expo_less_than_left_shift_amt}}) + (EXPO_WIDTH)'({subnormal&hidden_bit});
    end endgenerate

    //Output Selection
    always_comb begin
        fp_normalize_pre_processing_packet.sign_norm = sign;
        fp_normalize_pre_processing_packet.right_shift = right_shift;

        {expo_overflow_norm, expo_norm} = right_shift ? expo_norm_right_shift : expo_norm_left_shift;
        fp_normalize_pre_processing_packet.expo_overflow_norm = expo_overflow_norm;
        fp_normalize_pre_processing_packet.expo_norm = expo_norm;

        right = {frac_carry_bit, frac_safe_bit, hidden_bit, frac, grs};
        left = reverse(right);
        fp_normalize_pre_processing_packet.shifter_in = right_shift ? right : left;
        fp_normalize_pre_processing_packet.shift_amt = right_shift ? right_shift_amt : left_shift_amt_adjusted;

        fp_normalize_pre_processing_packet.valid = fp_normalize_packet.valid;
        fp_normalize_pre_processing_packet.rm = fp_normalize_packet.rm;
        fp_normalize_pre_processing_packet.id = fp_normalize_packet.id;
        fp_normalize_pre_processing_packet.fflags = fp_normalize_packet.fflags;
    end

    function logic [FRAC_WIDTH+3+GRS_WIDTH-1:0] reverse(input logic signed [FRAC_WIDTH+3+GRS_WIDTH-1:0] in);
        foreach(in[i])
            reverse[i] = in[FRAC_WIDTH+3+GRS_WIDTH-1-i];
    endfunction

endmodule
