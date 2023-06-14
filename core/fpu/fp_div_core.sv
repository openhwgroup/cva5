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

//TODO: calculate frac_width+2 bits of mantissa to satisfy correctly rounding
module fp_div_core
    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    import fpu_types::*;
(
    input logic                   clk,
    input logic                   rst,
    input fp_div_sqrt_inputs_t    fp_div_sqrt_inputs,
    input logic                   start_algorithm,
    fp_unit_writeback_interface.unit fp_wb
);

    unsigned_division_interface #(.DATA_WIDTH(2*FRAC_WIDTH+3)) div();
    unsigned_division_interface #(.DATA_WIDTH(FRAC_WIDTH+3)) div_shortened();
    logic                   start_algorithm_r;
    logic                   done[1:0];
    id_t                    id_in_progress;
    logic                   single;
    logic [FLEN-1:0]        rs1, rs2;
    logic                   rs1_hidden_bit, rs2_hidden_bit;
    logic                   rs1_sign, rs2_sign;
    logic [EXPO_WIDTH-1:0]  rs1_expo, rs2_expo;
    logic [EXPO_WIDTH-1:0]  rs1_left_shift_amt, rs2_left_shift_amt;
    logic                   rs1_normal, rs2_normal;
    logic [FRAC_WIDTH:0]    rs1_frac, rs2_frac;
    logic [2:0]             rm;
    logic                   rs1_is_inf, rs1_is_SNaN, rs1_is_QNaN, rs1_is_zero;
    logic                   rs2_is_inf, rs2_is_SNaN, rs2_is_QNaN, rs2_is_zero;
    logic                   early_terminate, invalid_operation, output_QNaN, output_zero, output_inf, div_by_zero;
    logic                   result_sign[1:0];
    logic                   result_hidden; //the integer part
    logic [EXPO_WIDTH+1:0] result_expo_intermediate[1:0], result_expo_intermediate_neg; //{sign, overflow, expo}
    logic right_shift;
    logic [EXPO_WIDTH-1:0] right_shift_amt;
    logic [EXPO_WIDTH:0] result_expo;
    logic [FRAC_WIDTH-1:0]  result_frac;
    logic [2:0]             grs;
    logic [FLEN-1:0] special_case_results[1:0];
    logic output_special_case[1:0];

    //Input pre-processing
    always_ff@(posedge clk) begin
        if (start_algorithm) begin
            rs1 <= fp_div_sqrt_inputs.rs1;
            rs2 <= fp_div_sqrt_inputs.rs2;
            rm <= fp_div_sqrt_inputs.rm;
            rs1_hidden_bit <= fp_div_sqrt_inputs.rs1_hidden_bit;
            rs2_hidden_bit <= fp_div_sqrt_inputs.rs2_hidden_bit;
            rs1_left_shift_amt <= fp_div_sqrt_inputs.rs1_pre_normalize_shift_amt;
            rs2_left_shift_amt <= fp_div_sqrt_inputs.rs2_pre_normalize_shift_amt;
            rs1_normal <= fp_div_sqrt_inputs.rs1_normal;
            rs2_normal <= fp_div_sqrt_inputs.rs2_normal;
            id_in_progress <= fp_div_sqrt_inputs.id;
            single <= fp_div_sqrt_inputs.single;
            rs1_is_inf <= fp_div_sqrt_inputs.rs1_special_case[3];
            rs1_is_SNaN <= fp_div_sqrt_inputs.rs1_special_case[2];
            rs1_is_QNaN <= fp_div_sqrt_inputs.rs1_special_case[1];
            rs1_is_zero <= fp_div_sqrt_inputs.rs1_special_case[0];
            rs2_is_inf <= fp_div_sqrt_inputs.rs2_special_case[3];
            rs2_is_SNaN <= fp_div_sqrt_inputs.rs2_special_case[2];
            rs2_is_QNaN <= fp_div_sqrt_inputs.rs2_special_case[1];
            rs2_is_zero <= fp_div_sqrt_inputs.rs2_special_case[0];
        end
    end

    //unpack
    assign rs1_sign    = rs1[FLEN-1];
    assign rs2_sign    = rs2[FLEN-1];
    assign rs1_expo    = rs1[FLEN-2-:EXPO_WIDTH] + EXPO_WIDTH'({~rs1_normal});
    assign rs2_expo    = rs2[FLEN-2-:EXPO_WIDTH] + EXPO_WIDTH'({~rs2_normal});
    assign rs1_frac    = {rs1_hidden_bit, rs1[0+:FRAC_WIDTH]};
    assign rs2_frac    = {rs2_hidden_bit, rs2[0+:FRAC_WIDTH]};

    //special case handling
    assign invalid_operation = (rs1_is_zero & rs2_is_zero) | (rs1_is_inf & rs2_is_inf) | rs1_is_SNaN | rs2_is_SNaN;
    assign div_by_zero       = ~rs1_is_zero & ~rs1_is_inf & ~rs1_is_QNaN & ~rs1_is_SNaN & rs2_is_zero;
    assign output_QNaN       = invalid_operation | rs1_is_QNaN | rs2_is_QNaN;
    assign output_inf        = ~output_QNaN & (div_by_zero | rs1_is_inf);
    generate if (ENABLE_SUBNORMAL) begin
        assign output_zero = ~output_QNaN & (rs1_is_zero | rs2_is_inf);
    end else begin
        assign output_zero = ~output_QNaN & (rs1_is_zero | ~rs1_normal | rs2_is_inf);
    end endgenerate
    assign early_terminate   = output_QNaN | output_inf | output_zero;
    assign result_sign[0]    = rs1_sign ^ rs2_sign;

    always_comb begin
        if(output_inf) begin
            special_case_results[0] = {result_sign[0], {(EXPO_WIDTH){1'b1}}, {(FRAC_WIDTH){1'b0}}};
        end else if (output_QNaN) begin
            special_case_results[0] = CANONICAL_NAN;
        end else begin //if (output_zero) begin
            special_case_results[0] = {result_sign[0], (FLEN-1)'(0)};
        end
    end

    //mantissa division
    assign div.dividend  = {rs1_frac, {(FRAC_WIDTH+2){1'b0}}};
    assign div.divisor   = {{(FRAC_WIDTH+2){1'b0}}, rs2_frac};
    assign div.start     = start_algorithm_r & ~early_terminate;     //start div if no special cases
    assign div.divisor_is_zero = rs2_is_zero;
    //fp_div_quick_clz #(FRAC_WIDTH+2) div_mantissa (.*);
    //fp_div_radix2 #(.DIV_WIDTH(2*FRAC_WIDTH+3)) div_mantissa (.*);

    assign div_shortened.dividend  = {rs1_frac, 2'b0};
    assign div_shortened.divisor   = {rs2_frac, 2'b0};
    assign div_shortened.start     = start_algorithm_r & ~early_terminate;     //start div if no special cases
    assign div_shortened.divisor_is_zero = rs2_is_zero;
    fp_div_radix4 #(.DIV_WIDTH(FRAC_WIDTH+3)) div_mantissa_shortened (.clk(clk), .rst(rst), .div(div_shortened));

    //assign {result_hidden, result_frac, grs[2:1]} = div.quotient[0+:FRAC_WIDTH+3];
    //assign grs[0] = |div.remainder;
    assign {result_hidden, result_frac, grs[2:1]} = div_shortened.quotient;
    assign grs[0] = div_shortened.remainder[0];//|div_shortened.remainder;

    //exponent handling
    generate if (ENABLE_SUBNORMAL) begin
        assign result_expo_intermediate[0] = ((EXPO_WIDTH+1)'(rs1_expo) - (EXPO_WIDTH+1)'(rs1_left_shift_amt)) -
                                            ((EXPO_WIDTH+1)'(rs2_expo) - (EXPO_WIDTH+1)'(rs2_left_shift_amt)) + BIAS;
        assign result_expo_intermediate_neg = -result_expo_intermediate[1];
        assign right_shift = result_expo_intermediate[1][EXPO_WIDTH+1] | (~|result_expo_intermediate[1][EXPO_WIDTH:0]);
        assign right_shift_amt = result_expo[EXPO_WIDTH-1:0] + EXPO_WIDTH'(right_shift);
        assign result_expo = right_shift ? result_expo_intermediate_neg[EXPO_WIDTH:0] : result_expo_intermediate[1][EXPO_WIDTH:0];
    end else begin
        assign result_expo_intermediate[0] = (EXPO_WIDTH+1)'(rs1_expo) - (EXPO_WIDTH+1)'(rs2_expo) + BIAS;
        assign result_expo_intermediate_neg = -result_expo_intermediate[1];
        assign right_shift = result_expo_intermediate[1][EXPO_WIDTH+1] | (~|result_expo_intermediate[1][EXPO_WIDTH:0]);
        assign right_shift_amt = result_expo[EXPO_WIDTH-1:0] + EXPO_WIDTH'(right_shift);
        assign result_expo = right_shift ? result_expo_intermediate_neg[EXPO_WIDTH:0] : result_expo_intermediate[1][EXPO_WIDTH:0];
    end endgenerate

    // calculate CLZ -> because 0.5 < result < 2, the shift amount is either 0 or 1
    logic[EXPO_WIDTH-1:0] left_shift_amt;
    assign left_shift_amt[EXPO_WIDTH-1:1] = '0;
    assign left_shift_amt[0] = ~result_hidden;

    logic advance;
    assign advance = ~fp_wb.done | fp_wb.ack;
    assign fp_wb.done = done[0];
    assign fp_wb.id = id_in_progress;
    assign fp_wb.d2s = single;
    assign fp_wb.fflags = {invalid_operation, div_by_zero, 3'b0};// ,|grs_round & ~early_terminate};
    assign fp_wb.rm = rm;
    assign fp_wb.rd = output_special_case[0] ? special_case_results[0] :
                                                {result_sign[0], result_expo[EXPO_WIDTH-1:0], result_frac[FRAC_WIDTH-1:0]};
    assign fp_wb.clz = output_special_case[0] ? 0 : left_shift_amt;
    assign fp_wb.hidden = result_hidden;
    assign fp_wb.safe = 1'b0;
    assign fp_wb.carry = 1'b0;
    assign fp_wb.grs = {grs & {3{~output_special_case[0]}}, {($bits(grs_t)-3){1'b0}}};

    assign fp_wb.expo_overflow = result_expo[EXPO_WIDTH] & ~output_special_case[0];
    assign fp_wb.subnormal = right_shift & ~output_special_case[0];
    assign fp_wb.right_shift = right_shift & ~output_special_case[0];
    assign fp_wb.right_shift_amt = right_shift_amt;

    //Registers
    always_ff @ (posedge clk) begin
        if (advance) begin
            done[0] <= (early_terminate & start_algorithm_r) | div_shortened.done;
            //pipeline
            result_sign[1] <= result_sign[0];
            result_expo_intermediate[1] <= result_expo_intermediate[0];
            start_algorithm_r <= start_algorithm;
            output_special_case[0] <= early_terminate;
            special_case_results[1] <= special_case_results[0];
        end
    end
endmodule
