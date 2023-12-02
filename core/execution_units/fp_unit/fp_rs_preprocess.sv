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

module fp_rs_preprocess

    import cva5_config::*;
    import fpu_types::*;

    #(
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )
    (
        input fp_t in, //Packed form
        input logic single,
        output fp_t double, //Only valid if input was single

        //Special cases
        output special_case_t special,
        output logic is_boxed,
        output logic hidden,
        output logic hidden_double,
        output logic hidden_single,

        //Pre normalization
        output fp_shift_amt_t prenormalize_shift,
        output frac_d_t prenormalize_frac
    );

    ////////////////////////////////////////////////////
    //Special case detection
    //Depends on the type of the input
    //Single precision must check NaN boxing
    logic inf_d, inf_s;
    logic snan_d, snan_s;
    logic qnan_d, qnan_s;
    logic zero_d, zero_s;

    assign is_boxed = &in.s.box;

    assign special.inf = single ? inf_s & is_boxed : inf_d;
    assign special.snan = single ? snan_s & is_boxed : snan_d;
    assign special.qnan = single ? qnan_s | ~is_boxed : qnan_d;
    assign special.zero = single ? zero_s & is_boxed : zero_d;
    assign hidden = single ? ~zero_s : hidden_double; //TODO: singles sharing subnormal range with doubles

    fp_special_case_detection #(.FRAC_W(FRAC_WIDTH_F), .EXPO_W(EXPO_WIDTH_F), .SUBNORMAL(1)) input_case_s (
        .expo(in.s.expo),
        .frac(in.s.frac),
        .is_inf(inf_s),
        .is_SNaN(snan_s),
        .is_QNaN(qnan_s),
        .is_zero(zero_s),
        .hidden(hidden_single)
    );
    fp_special_case_detection #(.FRAC_W(FRAC_WIDTH), .EXPO_W(EXPO_WIDTH), .SUBNORMAL(1)) input_case_d (
        .expo(in.d.expo),
        .frac(in.d.frac),
        .is_inf(inf_d),
        .is_SNaN(snan_d),
        .is_QNaN(qnan_d),
        .is_zero(zero_d),
        .hidden(hidden_double)
    );

    ////////////////////////////////////////////////////
    //Normalization
    //Done by shifting to set the implicit leading 1 (required by many execution units for subnormal numbers)
    //Does CLZ + shift in one cycle
    logic[EXPO_WIDTH_F-1:0] exponent_add;
    logic[FRAC_WIDTH-1:0] shift_arr;
    logic clz_hidden;
    logic[FRAC_WIDTH+1:0] clz_arr;
    logic[$clog2(FRAC_WIDTH+2)-1:0] clz_count;

    //Set up the array for shifting
    always_comb begin
        if (single) begin
            clz_hidden = hidden_single;
            shift_arr = '0;
            shift_arr[FRAC_WIDTH-1 -: FRAC_WIDTH_F] = in.s.frac;
        end
        else begin
            clz_hidden = hidden_double;
            shift_arr = in.d.frac;
        end
    end

    //Check leading zero to get shift count
    assign clz_arr = {clz_hidden, shift_arr, 1'b1}; //Pad to ensure the count is always accurate
    clz #(.WIDTH(FRAC_WIDTH+2)) frac_clz (
        .clz_input(clz_arr),
        .clz(clz_count),
        .zero()
    );
    
    //Do the normalization shift
    always_comb begin
        prenormalize_frac = shift_arr << clz_count;
        prenormalize_shift = '0;
        if (~single)
            prenormalize_shift[$clog2(FRAC_WIDTH)-1:0] = clz_count[$clog2(FRAC_WIDTH)-1:0];
        exponent_add = '0;
        exponent_add[$clog2(FRAC_WIDTH+2)-1:0] = clz_count;
    end


    ////////////////////////////////////////////////////
    //Single to Double
    //Scales exponent considering different ranges and shifting amounts
    //Uses normalized mantissa
    expo_d_t add_amt;
    expo_d_t bias_amt;
    expo_d_t expo_out;

    //Input case -> Output
    //Not NaN boxed -> CNaN
    //sNaN -> CNaN
    //qNaN -> CNaN
    //+-0 -> +-0
    //+-infty -> +-infty
    //subnormal -> not subnormal (this depends on relative widths)
    //regular -> regular

    //Sign
    assign double.d.sign = snan_s | qnan_s | ~is_boxed ? 1'b0 : in.s.sign;

    //Exponent
    assign add_amt = hidden_single ? {{(EXPO_WIDTH-EXPO_WIDTH_F){1'b0}}, in.s.expo} : -{{(EXPO_WIDTH-EXPO_WIDTH_F){1'b0}}, exponent_add};

    always_comb begin
        bias_amt = BIAS - BIAS_F;
        if (~hidden_single)
            bias_amt[0] = 1;
    end
    assign expo_out = bias_amt + add_amt;

    always_comb begin
        if (inf_s | snan_s | qnan_s | ~is_boxed)
            double.d.expo = '1;
        else if (zero_s)
            double.d.expo = '0;
        else
            double.d.expo = expo_out;
    end

    //Mantissa
    always_comb begin
        if (snan_s | qnan_s | ~is_boxed) //NaNs get canonicalized from s->d
            double.d.frac = {1'b1, {(FRAC_WIDTH-1){1'b0}}};
        else
            double.d.frac = prenormalize_frac;
    end

endmodule
