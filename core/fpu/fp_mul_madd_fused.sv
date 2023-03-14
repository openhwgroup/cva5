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

//TODO: underflow results in a 0: can deliver rounded subnormal instead
module fp_mul_madd_fused
    import taiga_config::*;
    import taiga_types::*;
    import l2_config_and_types::*;
    import fpu_types::*;

(
    input logic clk,
    input logic rst,
    input fp_madd_inputs_t fp_madd_inputs,
    unit_issue_interface.unit issue,
    //output fp_unit_writeback_t fp_wb,
    fp_unit_writeback_interface.unit fp_wb,
    //output [4:0] fflags,
    output fma_mul_outputs_t fma_mul_outputs
);

    parameter BIAS = {1'b0, {(EXPO_WIDTH-1){1'b1}}};
    logic [FLEN-1:0]               rs1;
    logic [FLEN-1:0]               rs2;
    logic [2:0]                    rm [4:0];
    logic [6:0]                    opcode [3:0];
    logic [2:0]                    instruction [3:0];

    logic                          rs1_hidden_bit;
    logic                          rs1_sign [2:0];
    logic [EXPO_WIDTH-1:0]         rs1_expo [2:0];
    logic [FRAC_WIDTH:0]           rs1_frac [2:0];

    logic                          rs2_hidden_bit;
    logic                          rs2_sign [2:0];
    logic [EXPO_WIDTH-1:0]         rs2_expo [2:0], pre_normalize_shift_amt[3:0];
    logic [EXPO_WIDTH-1:0]         rs3_expo;
    logic [FRAC_WIDTH:0]           rs2_frac [2:0];

    logic                          rs1_zero;
    logic                          rs2_zero;
    logic                          rs1_inf;
    logic                          rs2_inf;
    logic                          rs1_subnormal;
    logic                          rs2_subnormal;
    logic                          rs1_NaN;
    logic                          rs2_NaN;

    logic                          result_sign [1:0];
    logic [EXPO_WIDTH:0]           result_expo [1:0];
    logic                          possible_subnormal[1:0];
    logic [EXPO_WIDTH+1:0]         result_expo_intermediate;
    logic [EXPO_WIDTH+1:0]         result_expo_intermediate_neg;
    logic                          right_shift[1:0];
    logic [FRAC_WIDTH+1:0]         result_frac [1:0];
    logic [2*FRAC_WIDTH+2-1:0]     result_frac_intermediate;
    logic [FRAC_WIDTH-1:0]         residual_bits;
    logic [EXPO_WIDTH-1:0] clz_with_prepended_0s, left_shift_amt;
    logic [FLEN-1:0] special_case_results[1:0];
    logic output_special_case[1:0];

    logic [HALF_GRS_WIDTH-1:0]                          grs [1:0];
    logic                          output_QNaN [4:0];
    logic                          invalid_operation [4:0];
    logic                          output_inf[4:0];
    logic                          output_zero [4:0];
    logic                          done [3:0];
    id_t                           id [3:0];
    logic                          d2s [3:0];
    fp_unit_writeback_t            fma_mul_wb;
    logic [FLEN-1:0]               rs3 [3:0];
    logic                          rs3_hidden_bit[3:0];
    logic [3:0]                    rs3_special_case [3:0];
    logic [EXPO_WIDTH+1:0]           expo_diff;
    logic [EXPO_WIDTH+1:0]           expo_diff_negate;

    ////////////////////////////////////////////////////
    //Implementation
    assign rm[0] = fp_madd_inputs.rm;
    assign opcode[0] = fp_madd_inputs.op;
    assign instruction[0] = fp_madd_inputs.instruction;
    assign rs3[0] = fp_madd_inputs.rs3;
    assign rs3_hidden_bit[0] = fp_madd_inputs.rs3_hidden_bit;
    assign rs3_special_case[0] = fp_madd_inputs.rs3_special_case;
    assign rs1_sign[0] = rs1[FLEN-1];
    assign rs2_sign[0] = rs2[FLEN-1];
    assign rs1_expo[0] = rs1[FLEN-2-:EXPO_WIDTH];
    assign rs2_expo[0] = rs2[FLEN-2-:EXPO_WIDTH] + EXPO_WIDTH'(rs2_subnormal);
    assign rs1_frac[0] = {rs1_hidden_bit, rs1[FRAC_WIDTH-1:0]};
    assign rs2_frac[0] = {rs2_hidden_bit, rs2[FRAC_WIDTH-1:0]};
    assign rs1 = fp_madd_inputs.rs1;
    assign rs2 = fp_madd_inputs.rs2;
    assign rs1_hidden_bit = fp_madd_inputs.rs1_hidden_bit;
    assign rs2_hidden_bit = fp_madd_inputs.rs2_hidden_bit;
    assign rs1_subnormal = fp_madd_inputs.rs1_subnormal;
    assign rs2_subnormal = fp_madd_inputs.rs2_subnormal;
    assign pre_normalize_shift_amt[0] = fp_madd_inputs.rs2_pre_normalize_shift_amt;
    assign rs1_zero = fp_madd_inputs.rs1_special_case[0];
    assign rs2_zero = fp_madd_inputs.rs2_special_case[0];
    assign rs1_inf = fp_madd_inputs.rs1_special_case[3];
    assign rs2_inf = fp_madd_inputs.rs2_special_case[3];
    assign rs1_NaN = |fp_madd_inputs.rs1_special_case[2:1];
    assign rs2_NaN = |fp_madd_inputs.rs2_special_case[2:1];
    assign invalid_operation[0] = (rs1_zero & rs2_inf) | (rs1_inf & rs2_zero) | fp_madd_inputs.rs1_special_case[2] | fp_madd_inputs.rs2_special_case[2];
    assign output_QNaN[0] = invalid_operation[0] | rs1_NaN | rs2_NaN;
    assign output_inf[0] = ((rs1_inf & ~rs2_zero) | (~rs1_zero & rs2_inf)) & ~output_QNaN[0];
    generate if (ENABLE_SUBNORMAL)
        assign output_zero[0] = (rs1_zero | rs2_zero | (rs1_subnormal & rs2_subnormal)) & ~output_QNaN[0];
    else
        assign output_zero[0] = (rs1_zero | rs2_zero) & ~output_QNaN[0];
    endgenerate

    ////////////////////////////////////////////////////
    //multiplication
    //TODO: use DSP's pattern detect for zero result detection
    (* use_dsp = "no" *) unsigned_multiplier #(.WIDTH(FRAC_WIDTH+1)) mantissa_mul (
        .clk(clk),
        .rst(rst),
        .advance1(advance_stage[0]),
        .advance2(advance_stage[1]),
        .rs1(rs1_frac[0]),
        .rs2(rs2_frac[0]),
        .out(result_frac_intermediate)
    );

    generate if (ENABLE_SUBNORMAL) begin
        // negative intermediate expo -> subnormal result;
        // to normalize a subnormal result, the exponent is set to abs(intermediate expo), and the frac is right shifted for the same amount. Normalization handles driving the expo_norm to 0
        assign result_expo_intermediate =  {1'b0, rs1_expo[2]} + ({1'b0, rs2_expo[2]} - {2'b0, pre_normalize_shift_amt[2]}) - (EXPO_WIDTH+2)'(BIAS);
        assign result_expo_intermediate_neg = - result_expo_intermediate;
        assign right_shift[0] = result_expo_intermediate[EXPO_WIDTH+1] | (~|result_expo_intermediate[EXPO_WIDTH:0]);
        assign possible_subnormal[0] = right_shift[0];
        assign result_expo[0] = {result_expo_intermediate[EXPO_WIDTH+1] ? result_expo_intermediate_neg[EXPO_WIDTH:0] : result_expo_intermediate[EXPO_WIDTH:0]} & {(EXPO_WIDTH+1){~output_zero[2]}};
    end else begin
        // TODO: assert possible_subnormal to drive expo_norm 0 in normalization
        // the fraction does not need to be driven to 0 as special_case_detection only looks at exponent field
        assign result_expo_intermediate = ({1'b0, rs1_expo[2]} + {1'b0, rs2_expo[2]}) - (EXPO_WIDTH+2)'(BIAS);
        assign possible_subnormal[0] = result_expo_intermediate[EXPO_WIDTH+1];
        assign result_expo[0] = result_expo_intermediate[EXPO_WIDTH:0] & {(EXPO_WIDTH+1){~output_zero[2]}};
    end endgenerate

    always_comb begin
        result_sign[0] = rs1_sign[2] ^ rs2_sign[2];
        result_frac[0] = result_frac_intermediate[2*FRAC_WIDTH+2-1-:(2+FRAC_WIDTH)]; // {safe_bit, hidden_bit, fraction}
        residual_bits = result_frac_intermediate[0+:FRAC_WIDTH]; // bottom bits preserved for rounding
        grs[0] = {residual_bits[FRAC_WIDTH-1-:(HALF_GRS_WIDTH-1)], |residual_bits[0+:FRAC_WIDTH-(HALF_GRS_WIDTH-1)]};
    end

    ////////////////////////////////////////////////////
    //Output
    //pre-calculate clz for left shift
    generate if (FRAC_WIDTH+2 <= 32) begin
        localparam left_shift_amt_bias = (32 - (FRAC_WIDTH + 1));
        clz frac_clz (
            .clz_input (32'(result_frac[1])),
            .clz (clz_with_prepended_0s[4:0])
        );
        assign left_shift_amt = (clz_with_prepended_0s & {EXPO_WIDTH{~output_special_case[1]}}) - (left_shift_amt_bias & {EXPO_WIDTH{~output_special_case[1]}});
    end else begin
        localparam left_shift_amt_bias = (64 - (FRAC_WIDTH + 1));
        clz_tree frac_clz (
            .clz_input (64'(result_frac[1])),
            .clz (clz_with_prepended_0s[5:0])
        );
        assign left_shift_amt = (clz_with_prepended_0s & {EXPO_WIDTH{~output_special_case[1]}}) - (left_shift_amt_bias & {EXPO_WIDTH{~output_special_case[1]}});
    end endgenerate

    //Special case handling
    assign output_special_case[0] = output_inf[2] | output_QNaN[2] | output_zero[2];
    always_comb begin
        if(output_inf[3]) begin
            special_case_results[0] = {result_sign[1], {(EXPO_WIDTH){1'b1}}, {(FRAC_WIDTH){1'b0}}};
        end else if (output_QNaN[3]) begin
            special_case_results[0] = CANONICAL_NAN;
        end else if (output_zero[3]) begin
            special_case_results[0] = {result_sign[1], {(FLEN-1){1'b0}}};
        end else begin
            special_case_results[0] = {result_sign[1], (FLEN-1)'(0)};
        end
    end

    /* verilator lint_off UNOPTFLAT */
    logic advance_stage [3:0] ;
    assign advance_stage[0] = ~done[0] | advance_stage[1];
    assign advance_stage[1] = ~done[1] | advance_stage[2];
    //assign advance_stage[2] = ~done[2] | advance_stage[3];
    assign advance_stage[2] = fp_wb.ack | ~fp_wb.done;
    /* verilator lint_on UNOPTFLAT */

    //writeback
    assign issue.ready = advance_stage[0];
    assign fp_wb.done = done[2];
    assign fp_wb.id = id[2];
    assign fp_wb.d2s = d2s[2];
    assign fp_wb.fflags = {invalid_operation[3], 4'b0};//, |grs[1]};
    assign fp_wb.carry = 1'b0;
    assign fp_wb.safe = result_frac[1][FRAC_WIDTH+1];
    assign fp_wb.hidden = result_frac[1][FRAC_WIDTH];
    assign fp_wb.grs = output_special_case[1] ? 0 : {grs[1], {HALF_GRS_WIDTH{1'b0}}};
    assign fp_wb.rm = rm[3];
    assign fp_wb.clz = left_shift_amt;
    assign fp_wb.expo_overflow = result_expo[1][EXPO_WIDTH]&~output_special_case[1];
    assign fp_wb.rd = output_special_case[1] ? special_case_results[0] : {result_sign[1], result_expo[1][EXPO_WIDTH-1:0], result_frac[1][FRAC_WIDTH-1:0]};
    assign fp_wb.subnormal = possible_subnormal[1] & ~output_special_case[1];
    generate if (ENABLE_SUBNORMAL) begin
        assign fp_wb.right_shift = (right_shift[1] | result_frac[1][FRAC_WIDTH+1] & ~output_special_case[1]);
        // if the result is denormal, right shift frac by 1 extra position
        assign fp_wb.right_shift_amt = possible_subnormal[1] & ~output_special_case[1] ? result_expo[1][EXPO_WIDTH-1:0] + EXPO_WIDTH'(possible_subnormal[1]) : (EXPO_WIDTH)'(result_frac[1][FRAC_WIDTH+1]);
    end else begin
        // always righ shift by 1
        assign fp_wb.right_shift = result_frac[1][FRAC_WIDTH+1];
        assign fp_wb.right_shift_amt = (EXPO_WIDTH)'(result_frac[1][FRAC_WIDTH+1]);;
    end endgenerate

    //FMADD outputs
    //assign fma_mul_wb.rd = {result_sign_norm[0], result_expo_norm[0], result_frac_norm[0][0+:FRAC_WIDTH]};
    assign fma_mul_wb.done = done[1];
    assign fma_mul_wb.id = id[1];
    assign fma_mul_wb.rd = {result_sign[0], result_expo[0][EXPO_WIDTH-1:0], result_frac[0][FRAC_WIDTH-1-:FRAC_WIDTH]};
    assign fma_mul_outputs.is_fma = done[1] & instruction[2][2];
    assign fma_mul_outputs.mul_wb_rd_expo_overflow = result_expo[0][EXPO_WIDTH];
    assign fma_mul_outputs.mul_wb_rd_hidden = result_frac[0][FRAC_WIDTH+0];
    assign fma_mul_outputs.mul_wb_rd_safe = result_frac[0][FRAC_WIDTH+1];
    assign fma_mul_outputs.mul_wb = fma_mul_wb;
    assign fma_mul_outputs.mul_grs = {grs[0], {HALF_GRS_WIDTH{1'b0}}};
    assign fma_mul_outputs.mul_op = opcode[2][3];
    assign fma_mul_outputs.add_op = opcode[2][2];
    assign fma_mul_outputs.rs3 = rs3[2];
    assign fma_mul_outputs.rs2_special_case = rs3_special_case[2];
    assign fma_mul_outputs.rs3_hidden_bit = rs3_hidden_bit[2];
    assign fma_mul_outputs.mul_rm = rm[2];
    assign fma_mul_outputs.instruction = instruction[2];
    assign fma_mul_outputs.rs1_special_case = {output_inf[2], invalid_operation[2], output_QNaN[2], output_zero[2]};
    assign fma_mul_outputs.single = d2s[1];
    assign rs3_expo = rs3[2][FLEN-2-:EXPO_WIDTH];

    generate if (ENABLE_SUBNORMAL) begin
        // subnormal expo is implicitly 1
        assign expo_diff = result_expo[0] - ((EXPO_WIDTH+2)'(rs3_expo) + (EXPO_WIDTH+2)'({~rs3_hidden_bit[2]&~rs3_special_case[2][0]}));
        assign expo_diff_negate = ((EXPO_WIDTH+2)'(rs3_expo) + (EXPO_WIDTH+2)'({~rs3_hidden_bit[2]&~rs3_special_case[2][0]})) - result_expo[0];
        assign fma_mul_outputs.expo_diff = expo_diff[EXPO_WIDTH+1] ? expo_diff_negate[EXPO_WIDTH:0] : expo_diff[EXPO_WIDTH:0];
        assign fma_mul_outputs.swap = expo_diff[EXPO_WIDTH+1];
    end else begin
        assign expo_diff = (EXPO_WIDTH+2)'({result_expo[0] - rs3_expo});
        assign expo_diff_negate = (EXPO_WIDTH+2)'({rs3_expo - result_expo[0]});
        assign fma_mul_outputs.swap = expo_diff[EXPO_WIDTH];
        assign fma_mul_outputs.expo_diff = expo_diff[EXPO_WIDTH] ? expo_diff_negate[EXPO_WIDTH:0] : expo_diff[EXPO_WIDTH:0];
    end endgenerate

    always_ff @ (posedge clk) begin
        // mul1
        if (advance_stage[0]) begin
            done[0] <= issue.new_request;
            id[0] <= issue.id;
            d2s[0] <= fp_madd_inputs.fp_add_inputs.single;
            rm[1] <= rm[0];

            rs1_sign[1] <= rs1_sign[0];
            rs1_expo[1] <= rs1_expo[0];
            rs1_frac[1] <= rs1_frac[0];

            rs2_sign[1] <= rs2_sign[0];
            rs2_expo[1] <= rs2_expo[0];
            pre_normalize_shift_amt[1] <= pre_normalize_shift_amt[0];
            rs2_frac[1] <= rs2_frac[0];

            rs3[1] <= rs3[0];
            rs3_special_case[1] <= rs3_special_case[0];
            rs3_hidden_bit[1] <= rs3_hidden_bit[0];
            opcode[1] <= opcode[0];
            instruction[1] <= instruction[0];
            invalid_operation[1] <= invalid_operation[0];
            output_QNaN[1] <= output_QNaN[0];
            output_inf[1] <= output_inf[0];
            output_zero[1] <= output_zero[0];

        end
        // mul2
        if (advance_stage[1]) begin
            done[1] <= done[0];
            id[1] <= id[0];
            d2s[1] <= d2s[0];
            rm[2] <= rm[1];
            rs1_sign[2] <= rs1_sign[1];
            rs1_expo[2] <= rs1_expo[1];
            rs1_frac[2] <= rs1_frac[1];

            rs2_sign[2] <= rs2_sign[1];
            rs2_expo[2] <= rs2_expo[1];
            pre_normalize_shift_amt[2] <= pre_normalize_shift_amt[1];
            rs2_frac[2] <= rs2_frac[1];

            grs[1] <= grs[0];
            opcode[2] <= opcode[1];
            rs3[2] <= rs3[1];
            instruction[2] <= instruction[1];
            rs3_hidden_bit[2] <= rs3_hidden_bit[1];
            rs3_special_case[2] <= rs3_special_case[1];
            output_QNaN[2] <= output_QNaN[1];
            invalid_operation[2] <= invalid_operation[1];
            output_inf[2] <= output_inf[1];
            output_zero[2] <= output_zero[1];

        end
        //norm
        if (advance_stage[2]) begin
            done[2] <= done[1] & instruction[2][0]; //only FMUL instructions go the FMUL writeback path
            id[2] <= id[1];
            d2s[2] <= d2s[1];
            rm[3] <= rm[2];

            output_special_case[1] <= output_special_case[0];
            output_QNaN[3] <= output_QNaN[2];
            invalid_operation[3] <= invalid_operation[2];
            output_inf[3] <= output_inf[2];
            output_zero[3] <= output_zero[2];
            opcode[3] <= opcode[2];
            instruction[3] <= instruction[2];
            rs3[3] <= rs3[2];
            rs3_hidden_bit[3] <= rs3_hidden_bit[2];
            result_sign[1] <= result_sign[0];
            result_expo[1] <= result_expo[0];
            possible_subnormal[1] <= possible_subnormal[0];
            pre_normalize_shift_amt[3] <= pre_normalize_shift_amt[2];
            right_shift[1] <= right_shift[0];
            result_frac[1] <= result_frac[0];
        end
        //round1
        if (advance_stage[3]) begin
            done[3] <= done[2];
            id[3] <= id[2];
            rm[4] <= rm[3];
            invalid_operation[4] <= invalid_operation[3];
            output_QNaN[4] <= output_QNaN[3];
            output_inf[4] <= output_inf[3];
            output_zero[4] <= output_zero[3];
        end
    end

endmodule
