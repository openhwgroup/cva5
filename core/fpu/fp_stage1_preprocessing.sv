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

module fp_stage1_preprocessing
    import taiga_config::*;
    import fpu_types::*;

(
    input fp_t in, //Packed form
    input logic single,
    output fp_t double, //Only valid if input was single

    //Special cases
    output logic is_inf,
    output logic is_SNaN,
    output logic is_QNaN,
    output logic is_zero,
    output logic is_boxed,
    output logic hidden,
    output logic hidden_double,
    output logic hidden_single,

    //Pre normalization
    input logic prenormalize,
    output logic[EXPO_WIDTH-1:0] prenormalize_shift, //TODO: Make this smaller
    output logic prenormalize_hidden,
    output logic[FRAC_WIDTH-1:0] prenormalize_frac
);

    localparam MAX_SHIFTS = BIAS-BIAS_F;

    //Input case -> Output
    //Not NaN boxed -> CNaN
    //sNaN -> CNaN
    //qNaN -> CNaN
    //+-0 -> +-0
    //+-infty -> +-infty
    //subnormal -> not subnormal (this depends on relative widths)
    //regular -> regular

    //Canonical NaN = {1'b0, {(EXPO_W-1){1'b1}}, 1'b1, {(FRAC_W-2){1'b0}}};


    //Special cases
    logic inf_d, inf_s;
    logic snan_d, snan_s;
    logic qnan_d, qnan_s;
    logic zero_d, zero_s;

    assign is_inf = single ? inf_s & is_boxed : inf_d;
    assign is_SNaN = single ? snan_s & is_boxed : snan_d;
    assign is_QNaN = single ? qnan_s | ~is_boxed : qnan_d;
    assign is_zero = single ? zero_s & is_boxed : zero_d;
    assign hidden = single ? ~zero_s : hidden_double; //TODO: singles sharing subnormal range with doubles

    fp_special_case_detection #(.FRAC_W(FRAC_WIDTH_F), .EXPO_W(EXPO_WIDTH_F)) input_case_s (
        .data_in(in.raw[FLEN_F-1:0]),
        .is_inf(inf_s),
        .is_SNaN(snan_s),
        .is_QNaN(qnan_s),
        .is_zero(zero_s),
        .hidden(hidden_single)
    );
    fp_special_case_detection #(.FRAC_W(FRAC_WIDTH), .EXPO_W(EXPO_WIDTH)) input_case_d (
        .data_in(in.raw),
        .is_inf(inf_d),
        .is_SNaN(snan_d),
        .is_QNaN(qnan_d),
        .is_zero(zero_d),
        .hidden(hidden_double)
    );

    //Pack inputs/outputs
    //Upper bits must all be 1 otherwise the input is not a float
    generate if (FLEN > FLEN_F)
        assign is_boxed = &in.s.box;
    else
        assign is_boxed = 1;
    endgenerate


    logic[EXPO_WIDTH_F-1:0] exponent_add;
    generate
        if (ENABLE_SUBNORMAL) begin
            logic[FRAC_WIDTH:0] shift_arr;
            always_comb begin
                if (single) begin
                    shift_arr = '0;
                    shift_arr[FRAC_WIDTH] = hidden_single;
                    if (is_boxed)
                        shift_arr[FRAC_WIDTH-1 -: FRAC_WIDTH_F] = in.s.frac;
                    else //TODO: Does this matter?
                        shift_arr[FRAC_WIDTH-1] = 1;
                end
                else
                    shift_arr = {hidden_double, in.d.frac};
            end

            logic[FRAC_WIDTH+1:0] clz_arr;
            logic[$clog2(FRAC_WIDTH+2)-1:0] clz_count;
            assign clz_arr = {shift_arr, 1'b1};

            clz_tree #(.WIDTH(FRAC_WIDTH+2)) frac_clz (
                .clz_input(clz_arr),
                .clz(clz_count),
                .zero()
            );

            logic[$clog2(FRAC_WIDTH+2)-1:0] shift_amount;
            always_comb begin //TODO: Edge case where frac widths are close for singles that aren't enabled (MAX_SHIFTS)
                shift_amount = single | prenormalize ? clz_count : '0;
                {prenormalize_hidden, prenormalize_frac} = shift_arr << shift_amount;
                prenormalize_shift = '0;
                if (~single)
                    prenormalize_shift[$clog2(FRAC_WIDTH)-1:0] = shift_amount[$clog2(FRAC_WIDTH)-1:0];
                exponent_add = '0;
                exponent_add[$clog2(FRAC_WIDTH+2)-1:0] = clz_count;
            end

        end
        else begin
            assign prenormalize_shift = '0;
            assign prenormalize_hidden = single ? hidden_single : hidden_double; //TODO: just 1?
            assign prenormalize_frac = single ? {in.s.frac, {(FRAC_WIDTH-FRAC_WIDTH_F){1'b0}}} : double.d.frac;
            assign exponent_add = '0;
        end
    endgenerate


    assign double.d.sign = snan_s | qnan_s | ~is_boxed ? 1'b0 : in.s.sign;
    logic[EXPO_WIDTH-1:0] expo_out;
    logic[EXPO_WIDTH-1:0] add_amt;
    assign add_amt = hidden_single ? {{(EXPO_WIDTH-EXPO_WIDTH_F){1'b0}}, in.s.expo} : -{{(EXPO_WIDTH-EXPO_WIDTH_F){1'b0}}, exponent_add};
    

    logic[EXPO_WIDTH-1:0] bias_amt;
    always_comb begin
        bias_amt = BIAS - BIAS_F;
        if (~hidden_single)
            bias_amt[0] = 1;
    end
    assign expo_out = bias_amt + add_amt;

    //Exponent
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
        if (snan_s | qnan_s | ~is_boxed) //nans get canonicalized from s->d
            double.d.frac = {1'b1, {(FRAC_WIDTH-1){1'b0}}};
        else
            double.d.frac = prenormalize_frac;
    end

endmodule
