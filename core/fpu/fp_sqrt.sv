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

module fp_sqrt
    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    import fpu_types::*;

(
    input logic clk,
    input logic rst,
    unit_issue_interface.unit issue,
    input fp_div_sqrt_inputs_t fp_div_sqrt_inputs,
    fp_unit_writeback_interface.unit wb
);
    typedef struct packed{
        id_t id;
    } sqrt_attributes_t;

    typedef struct packed{
        logic [FLEN-1:0] radicand;
        sqrt_attributes_t attr;
        logic hidden_bit;
        logic [3:0] special_case;
        logic [EXPO_WIDTH-1:0] left_shift_amt;
        logic expo_overflow;
    } sqrt_fifo_inputs_t;
    parameter ITERATION = FRAC_WIDTH+1+3;

    ////////////////////////////////////////////////////
    //Special Case and Exception Handling
    logic is_inf, is_SNaN, is_zero, is_QNaN;
    logic invalid_operation;
    logic output_QNaN;
    logic output_zero;
    logic output_inf;
    logic output_one;
    logic early_terminate;
    logic [FLEN-1:0] early_terminate_result;
    logic [2:0] rm;

    assign {is_inf, is_SNaN, is_QNaN, is_zero} = sqrt_op.special_case;
    assign invalid_operation = rs1_sign & ~is_zero;
    assign output_inf = is_inf & ~rs1_sign;
    assign output_QNaN = is_SNaN | is_QNaN | invalid_operation;
    assign output_zero = is_zero;
    assign output_one = rs1_expo[EXPO_WIDTH-1:0] == {1'b0, {(EXPO_WIDTH-1){1'b1}}} & ~|rs1[0+:FRAC_WIDTH] & ~rs1_sign;
    assign early_terminate = output_inf | output_zero | output_QNaN | output_one;

    always_comb begin
        if (output_QNaN)
            early_terminate_result = CANONICAL_NAN;
        else if (output_inf)
            early_terminate_result = {1'b0, {EXPO_WIDTH{1'b1}}, FRAC_WIDTH'(0)};
        else if (output_zero)
            early_terminate_result = {fp_div_sqrt_inputs.rs1[FLEN-1], (FRAC_WIDTH+EXPO_WIDTH)'(0)};
        else
            early_terminate_result = {2'b0, {(EXPO_WIDTH-1){1'b1}}, FRAC_WIDTH'(0)};
    end

    ////////////////////////////////////////////////////
    //Input FIFO and denormal pre-normalization
    logic [EXPO_WIDTH-1:0] left_shift_amt;
    logic [FRAC_WIDTH:0] frac_normalized;
    logic [EXPO_WIDTH:0] expo_normalized;
    sqrt_fifo_inputs_t fifo_inputs;

    generate if (ENABLE_SUBNORMAL) begin
        assign left_shift_amt = fp_div_sqrt_inputs.rs1_pre_normalize_shift_amt;
        assign frac_normalized = {fp_div_sqrt_inputs.rs1_hidden_bit, fp_div_sqrt_inputs.rs1[0+:FRAC_WIDTH]};
        assign expo_normalized = fp_div_sqrt_inputs.rs1[FLEN-2-:EXPO_WIDTH] + EXPO_WIDTH'({~fp_div_sqrt_inputs.rs1_normal}) - left_shift_amt; //denormal expo == 1, and subtract pre-normalized shift amount
        assign fifo_inputs.expo_overflow = expo_normalized[EXPO_WIDTH];
        assign fifo_inputs.radicand = {fp_div_sqrt_inputs.rs1[FLEN-1], expo_normalized[EXPO_WIDTH-1:0], frac_normalized[FRAC_WIDTH-1:0]};
        assign fifo_inputs.left_shift_amt = left_shift_amt;
    end else begin
        assign fifo_inputs.radicand = fp_div_sqrt_inputs.rs1;
    end endgenerate
    assign fifo_inputs.attr.id = issue.id;
    assign fifo_inputs.hidden_bit = fp_div_sqrt_inputs.rs1_hidden_bit;
    assign fifo_inputs.special_case = fp_div_sqrt_inputs.rs1_special_case;

    fifo_interface #(.DATA_WIDTH($bits(sqrt_fifo_inputs_t))) input_fifo();
    taiga_fifo #(.DATA_WIDTH($bits(sqrt_fifo_inputs_t)), .FIFO_DEPTH(1)) sqrt_input_fifo (
        .clk (clk),
        .rst (rst),
        .fifo (input_fifo)
    );

    sqrt_fifo_inputs_t sqrt_op;
    assign input_fifo.data_in = fifo_inputs;
    assign input_fifo.push = issue.new_request;
    assign input_fifo.potential_push = issue.new_request;
    assign input_fifo.pop = input_fifo.valid & ~in_progress;
    assign issue.ready = ~input_fifo.full | input_fifo.pop;
    assign sqrt_op = input_fifo.data_out;

    //If more than one cycle, set in_progress so that multiple div.start signals are not sent to the div unit.
    logic in_progress;
    set_clr_reg_with_rst #(.SET_OVER_CLR(1), .WIDTH(1), .RST_VALUE('0)) in_progress_m (
        .clk, .rst,
        .set(input_fifo.valid & (~in_progress)),
        .clr(wb.ack),
        .result(in_progress)
    );

    sqrt_attributes_t in_progress_attr;
    always_ff @ (posedge clk) begin
        if (input_fifo.pop)
            in_progress_attr <= sqrt_op.attr;
        if (issue.new_request)
            rm <= fp_div_sqrt_inputs.rm;
    end
    ////////////////////////////////////////////////////
    //sqrt mantissa core
    logic [FLEN-1:0] rs1;
    logic rs1_sign;
    logic [FRAC_WIDTH:0] rs1_frac;
    logic [EXPO_WIDTH:0] rs1_expo;
    logic rs1_expo_overflow;
    logic odd_exponent;
    logic [FRAC_WIDTH+3:0] sqrt_mantissa_input_odd_expo, sqrt_mantissa_input_even_expo, frac_sqrt;
    logic [FRAC_WIDTH:0] result_frac[1:0];
    logic [2:0] grs[1:0];
    unsigned_sqrt_interface #(.DATA_WIDTH(FRAC_WIDTH+4)) sqrt(); //DATA_WIDTH has to be power of 2

    assign rs1 = sqrt_op.radicand;
    assign rs1_sign = rs1[FLEN-1];
    assign rs1_expo_overflow = sqrt_op.expo_overflow;
    assign rs1_expo = {rs1_expo_overflow, rs1[FLEN-2-:EXPO_WIDTH]};
    assign odd_exponent = ~rs1_expo[0];
    assign rs1_frac = {1'b1, rs1[0+:FRAC_WIDTH]}; //hidden bit is always 1 since denormals are pre-normalized
    assign sqrt_mantissa_input_odd_expo = {4'b00, rs1_frac[FRAC_WIDTH:1]};
    assign sqrt_mantissa_input_even_expo = {3'b0, rs1_frac};
    assign sqrt.radicand = odd_exponent ? sqrt_mantissa_input_odd_expo : sqrt_mantissa_input_even_expo;
    assign sqrt.start = input_fifo.pop;// & ~early_terminate;//input_fifo.valid & (~in_progress);
    assign sqrt.early_terminate = early_terminate;

    sqrt_mantissa #(.ITERATION(ITERATION)) sqrt_block (
        .clk (clk),
        .rst (rst),
        .sqrt (sqrt)
    );

    assign frac_sqrt = sqrt.quotient;
    assign {result_frac[0], grs[0]} = frac_sqrt;//sqrt.quotient;

    ////////////////////////////////////////////////////
    //Sign and Exponent handling
    logic odd_exponent_r;
    logic [EXPO_WIDTH:0] rs1_expo_r;
    logic result_expo_overflow;
    logic [EXPO_WIDTH-1:0] result_expo;

    always_ff @ (posedge clk) begin
        if (sqrt.start) begin
            rs1_expo_r <= {sqrt_op.expo_overflow, rs1[FLEN-2-:EXPO_WIDTH]};
        end
    end

    generate if (ENABLE_SUBNORMAL) begin
        logic [EXPO_WIDTH:0] unbiased_expo, unbiased_expo_abs, unbiased_result_expo_abs, unbiased_result_expo;
        assign odd_exponent_r = ~rs1_expo_r[0];//unbiased_expo[0];
        assign unbiased_expo = rs1_expo_r - EXPO_WIDTH'(odd_exponent_r) - BIAS;
        assign unbiased_expo_abs = unbiased_expo[EXPO_WIDTH] ? -unbiased_expo : unbiased_expo;
        assign unbiased_result_expo_abs = unbiased_expo_abs >> 1;
        assign unbiased_result_expo = unbiased_expo[EXPO_WIDTH] ? -unbiased_result_expo_abs : unbiased_result_expo_abs;
        assign {result_expo_overflow, result_expo} = unbiased_result_expo + BIAS;
    end else begin
        logic [EXPO_WIDTH:0] unbiased_expo, unbiased_expo_abs, unbiased_result_expo_abs, unbiased_result_expo;
        assign odd_exponent_r = ~rs1_expo_r[0];//unbiased_expo[0];
        assign unbiased_expo = rs1_expo_r - EXPO_WIDTH'(odd_exponent_r) - BIAS;
        assign unbiased_expo_abs = unbiased_expo[EXPO_WIDTH-1] ? -unbiased_expo : unbiased_expo;
        assign unbiased_result_expo_abs = unbiased_expo_abs >> 1;
        assign unbiased_result_expo = unbiased_expo[EXPO_WIDTH-1] ? -unbiased_result_expo_abs : unbiased_result_expo_abs;
        assign {result_expo_overflow, result_expo} = unbiased_result_expo + BIAS;
    end endgenerate

    ////////////////////////////////////////////////////
    assign wb.done = done_r;// | sqrt.done;
    assign wb.id = in_progress_attr.id;
    assign wb.grs = {{grs[0][2:1], grs[0][0] | |sqrt.remainder}, {($bits(grs_t)-3){1'b0}}};
    assign wb.fflags = {invalid_operation, 3'b000, |grs[0]};
    assign wb.rm = rm;
    assign wb.carry = 0;
    assign wb.safe = 0;
    assign wb.hidden = result_frac[0][FRAC_WIDTH];
    assign wb.rd = early_terminate ? early_terminate_result : {rs1_sign, result_expo, result_frac[0][0+:FRAC_WIDTH]};

    ////////////////////////////////////////////////////
    //Output
    logic done_r;
    always_ff @ (posedge clk) begin
        if (wb.ack)
            done_r <= 0;
        else if (sqrt.done)// | (early_terminate & input_fifo.pop))
            done_r <= 1;
    end
    ////////////////////////////////////////////////////
    //Register
    always_ff @ (posedge clk) begin
        result_frac[1] <= result_frac[0];
        grs[1] <= grs[0];
    end
endmodule
