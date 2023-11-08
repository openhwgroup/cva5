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

module fp_mul

    import cva5_config::*;
    import cva5_types::*;
    import fpu_types::*;

    #(
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )
    (
        input logic clk,
        input logic rst,
        input fp_mul_inputs_t mul_args,
        input logic fma,
        input fp_fma_inputs_t fma_args,
        unit_issue_interface.unit issue,
        fp_intermediate_wb_interface.unit wb,
        input logic add_ready,
        output logic add_valid,
        output id_t add_id,
        output fp_add_inputs_t add_args
    );

    localparam HALF_GRS_WIDTH = GRS_WIDTH/2;

    logic advance_to_mul2;
    logic advance_to_final;

    /////////////////////////////////////////////
    //Cycle 1
    //Half of the multiplication
    //Special case detection
    logic nv[2:0];
    logic inf[2:0];
    logic qnan[2:0];
    logic true_zero[2:0];
    logic subnormal_zero[2:0];

    assign nv[0] = (mul_args.rs1_special_case.zero & mul_args.rs2_special_case.inf) | (mul_args.rs1_special_case.inf & mul_args.rs2_special_case.zero) | mul_args.rs1_special_case.snan | mul_args.rs2_special_case.snan;
    assign qnan[0] = nv[0] | mul_args.rs1_special_case.snan | mul_args.rs1_special_case.qnan | mul_args.rs2_special_case.snan | mul_args.rs2_special_case.qnan;
    assign inf[0] = ((mul_args.rs1_special_case.inf & ~mul_args.rs2_special_case.zero) | (~mul_args.rs1_special_case.zero & mul_args.rs2_special_case.inf)) & ~qnan[0];
    assign true_zero[0] = (mul_args.rs1_special_case.zero | mul_args.rs2_special_case.zero) & ~qnan[0];
    //The exponent logic can only handle 1 subnormal argument. 2 subnormals produces 0 mantissa but a set sticky bit
    assign subnormal_zero[0] = ~mul_args.rs1_hidden & ~mul_args.rs2_hidden & ~true_zero[0];

    //Unpacking
    id_t id[2:0];
    rm_t rm[2:0];
    logic d2s[2:0];
    logic sign_xor[2:0];
    expo_d_t rs1_expo[1:0];
    expo_d_t rs2_expo[1:0];
    fp_shift_amt_t rs2_prenormalize_shift_amt[1:0];
    fp_fma_inputs_t fma_info[2:0];

    assign id[0] = issue.id;
    assign rm[0] = mul_args.rm;
    assign d2s[0] = mul_args.single;
    assign sign_xor[0] = mul_args.rs1.d.sign ^ mul_args.rs2.d.sign;
    assign rs1_expo[0] = mul_args.rs1.d.expo;
    assign rs2_expo[0] = mul_args.rs2.d.expo + {{(EXPO_WIDTH-1){1'b0}}, ~mul_args.rs2_hidden};
    assign rs2_prenormalize_shift_amt[0] = mul_args.rs2_prenormalize_shift_amt;
    assign fma_info[0] = fma_args;

    //Pipelining
    logic valid_r;
    logic fma_r;

    assign advance_to_mul2 = ~valid_r | advance_to_final;

    always_ff @(posedge clk) begin
        if (rst)
            valid_r <= 0;
        else if (advance_to_mul2)
            valid_r <= issue.new_request;

        if (advance_to_mul2) begin
            fma_r <= fma;
            id[1] <= id[0];
            rm[1] <= rm[0];
            d2s[1] <= d2s[0];
            sign_xor[1] <= sign_xor[0];
            rs1_expo[1] <= rs1_expo[0];
            rs2_expo[1] <= rs2_expo[0];
            rs2_prenormalize_shift_amt[1] <= rs2_prenormalize_shift_amt[0];
            fma_info[1] <= fma_info[0];

            nv[1] <= nv[0];
            qnan[1] <= qnan[0];
            inf[1] <= inf[0];
            true_zero[1] <= true_zero[0];
            subnormal_zero[1] <= subnormal_zero[0];
        end
    end

    ////////////////////////////////////////////////////
    //Multiplication itself
    //Pipelined over 2 cycles
    logic[FRAC_WIDTH:0] mul_in1;
    logic[FRAC_WIDTH:0] mul_in2;
    logic[2*FRAC_WIDTH+2-1:0] intermediate_frac;

    always_ff @(posedge clk) begin
        if (advance_to_mul2) begin
            mul_in1 <= {1'b1, mul_args.rs1.d.frac};
            mul_in2 <= {1'b1, mul_args.rs2.d.frac};
        end
        if (advance_to_final)
            intermediate_frac <= mul_in1 * mul_in2;
    end

    /////////////////////////////////////////////
    //Cycle 2
    //Second half of the multiplication
    //Exponent logic depends on the presence of subnormal numbers
    logic[EXPO_WIDTH+1:0] signed_expo;
    logic[EXPO_WIDTH:0] neg_signed_expo;
    logic[EXPO_WIDTH:0] intermediate_expo;
    logic intermediate_expo_is_zero;

    //Negative intermediate expo -> subnormal result
    //To normalize a subnormal result, the exponent is set to abs(intermediate expo), and the frac is right shifted for the same amount. Normalization handles driving the expo_norm to 0
    assign signed_expo = {1'b0, rs1_expo[1]} + ({1'b0, rs2_expo[1]} - {1'b0, rs2_prenormalize_shift_amt[1]}) - {2'b0, {(EXPO_WIDTH-1){1'b1}}};
    assign neg_signed_expo = -signed_expo[EXPO_WIDTH:0];
    assign intermediate_expo = signed_expo[EXPO_WIDTH+1] ? neg_signed_expo : signed_expo[EXPO_WIDTH:0];
    assign intermediate_expo_is_zero = ~|signed_expo;

    //Pipelining
    logic result_expo_overflow;
    expo_d_t result_expo;
    logic[EXPO_WIDTH+1:0] result_expo_diff;
    logic result_expo_is_negative;
    logic result_expo_is_zero;
    logic output_special;

    assign advance_to_final = (wb.done & wb.ack) | (~wb.done & ~add_valid) | (add_valid & add_ready);

    always_ff @ (posedge clk) begin
        if (rst) begin
            wb.done <= 0;
            add_valid <= 0;
        end
        else if (advance_to_final) begin
            wb.done <= valid_r & ~fma_r;
            add_valid <= valid_r & fma_r;
        end

        if (advance_to_final) begin
            id[2] <= id[1];
            d2s[2] <= d2s[1];
            rm[2] <= rm[1];
            sign_xor[2] <= sign_xor[1];
            nv[2] <= nv[1];
            qnan[2] <= qnan[1];
            inf[2] <= inf[1];
            true_zero[2] <= true_zero[1];
            subnormal_zero[2] <= subnormal_zero[1];
            output_special <= inf[1] | qnan[1] | true_zero[1] | subnormal_zero[1];
            fma_info[2] <= fma_info[1];

            result_expo_overflow <= intermediate_expo[EXPO_WIDTH];
            result_expo_is_negative <= signed_expo[EXPO_WIDTH+1];
            result_expo_is_zero <= intermediate_expo_is_zero;
            result_expo <= intermediate_expo[EXPO_WIDTH-1:0];
            result_expo_diff <= signed_expo;
        end
    end

    /////////////////////////////////////////////
    //Output
    //Finalize multiplication outputs
    //Create FMA arguments
    logic result_safe;
    logic result_hidden;
    frac_d_t result_frac;
    logic[HALF_GRS_WIDTH-1:0] result_grs;
    logic result_is_subnormal;

    assign {result_safe, result_hidden, result_frac} = intermediate_frac[2*FRAC_WIDTH+2-1-:2+FRAC_WIDTH];
    //There is no reduction for the full grs, but this accommodates optional intermediate rounding
    assign result_grs = {intermediate_frac[FRAC_WIDTH-1-:HALF_GRS_WIDTH-1], |intermediate_frac[FRAC_WIDTH-HALF_GRS_WIDTH:0]};

    assign result_is_subnormal = result_expo_is_negative | (result_expo_is_zero & ~result_safe);

    //Special case handling
    fp_t special_result;

    always_comb begin
        if (inf[2]) begin
            special_result.d.sign = sign_xor[2];
            special_result.d.expo = '1;
            special_result.d.frac = '0;
        end
        else if (qnan[2])
            special_result.raw = CANONICAL_NAN;
        else begin //Zero
            special_result.d.sign = sign_xor[2];
            special_result.d.expo = '0;
            special_result.d.frac = '0;
        end
    end

    assign issue.ready = advance_to_mul2;

    //Writeback
    assign wb.id = id[2];
    assign wb.d2s = d2s[2];
    assign wb.fflags.nv = nv[2];
    assign wb.fflags.of = 0;
    assign wb.fflags.uf = 0;
    assign wb.fflags.dz = 0;
    assign wb.fflags.nx = 0; //Will be set by normalization
    assign wb.carry = 0;
    assign wb.safe = result_safe;
    assign wb.hidden = output_special ? qnan[2] | inf[2] : result_hidden;
    assign wb.clz = '0;
    assign wb.ignore_max_expo = output_special;
    always_comb begin
        wb.grs = '0;
        if (subnormal_zero[2])
            wb.grs[0] = 1'b1; //Result is some nonzero number - set sticky
        else if (~output_special)
            wb.grs[GRS_WIDTH-1-:HALF_GRS_WIDTH] = result_grs;

        if (output_special)
            wb.rd = special_result;
        else begin
            wb.rd.d.sign = sign_xor[2];
            wb.rd.d.expo = result_expo;
            wb.rd.d.frac = result_frac;
        end
    end
    assign wb.rm = rm[2];
    assign wb.expo_overflow = result_expo_overflow & ~output_special;
    assign wb.subnormal = result_is_subnormal & ~output_special;
    assign wb.right_shift = (result_is_subnormal | result_safe) & ~output_special;
    //If the result is subnormal, right shift frac by 1 extra position
    assign wb.right_shift_amt = result_is_subnormal ? result_expo+1 : 1;

    //FMA args
    assign add_id = id[2];
    assign add_args.rm = rm[2];
    assign add_args.single = d2s[2];
    assign add_args.add = fma_info[2].add_sign;
    assign add_args.rs1_expo_overflow = wb.expo_overflow;
    assign add_args.fp_add_grs = wb.grs;
    assign add_args.rs1.d.sign = wb.rd.d.sign ^ fma_info[2].mul_sign;
    assign add_args.rs1.d.expo = result_expo_is_negative ? '0 : wb.rd.d.expo;
    assign add_args.rs1.d.frac = wb.rd.d.frac;
    assign add_args.rs1_hidden = wb.hidden;
    assign add_args.rs1_safe = wb.safe & ~subnormal_zero[2];
    assign add_args.rs1_special_case.zero = true_zero[2] | subnormal_zero[2];
    assign add_args.rs1_special_case.inf = inf[2];
    assign add_args.rs1_special_case.qnan = qnan[2];
    assign add_args.rs1_special_case.snan = nv[2];
    
    assign add_args.rs2 = fma_info[2].rs3;
    assign add_args.rs2_hidden = fma_info[2].rs3_hidden;
    assign add_args.rs2_safe = 0;
    assign add_args.rs2_special_case = fma_info[2].rs3_special_case;

    //Compare exponents for swapping
    logic rs3_add;
    logic[EXPO_WIDTH+1:0] expo_diff;
    logic[EXPO_WIDTH:0] expo_diff_negate;
    logic[EXPO_WIDTH+1:0] expo_diff_rs1;

    assign rs3_add = ~fma_info[2].rs3_hidden;
    assign expo_diff_rs1 = result_expo_is_negative & ~output_special ? result_expo_diff : {1'b0, wb.expo_overflow, wb.rd.d.expo};
    assign expo_diff = expo_diff_rs1 - ({2'b0, fma_info[2].rs3.d.expo} + {{(EXPO_WIDTH){1'b0}}, 1'b0, rs3_add});
    assign expo_diff_negate = -expo_diff[EXPO_WIDTH:0];
    assign add_args.expo_diff = expo_diff[EXPO_WIDTH+1] ? expo_diff_negate : expo_diff[EXPO_WIDTH:0];
    assign add_args.swap = expo_diff[EXPO_WIDTH+1];

endmodule
