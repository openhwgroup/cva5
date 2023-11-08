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

module fp_wb2int_misc

    import cva5_config::*;
    import cva5_types::*;
    import fpu_types::*;

    (
        input logic clk,
        input logic rst,
        input fp_wb2int_misc_inputs_t args,
        unit_issue_interface.unit issue,
        unit_writeback_interface.unit wb,
        output fflags_t fflags
    );

    ////////////////////////////////////////////////////
    //Implementation
    //Comparisons, classifications, conversions to integer, and moves sharing a single writeback port
    //Implemented as a 2 cycle pipeline (though only the conversion needs the second cycle)
    logic advance;
    assign advance = wb.ack | ~wb.done;
    assign issue.ready = advance;

    always_ff @(posedge clk) begin
        if (rst)
            wb.done <= 0;
        else begin
            if (issue.new_request)
                wb.done <= 1;
            else if (wb.ack)
                wb.done <= 0;
        end
        
        if (issue.new_request)
            wb.id <= issue.id;
    end

    ////////////////////////////////////////////////////
    //FMV
    //Transfers bits unchanged from an FP register to an INT register
    //This instruction is meant to transfer single precision numbers, so in reduced precision only the single precision bits are used
    logic[31:0] fmv_rd;
    always_comb begin
        fmv_rd = '0;
        fmv_rd[FLEN_F-1:0] = args.rs1.raw[FLEN_F-1:0];
    end

    ////////////////////////////////////////////////////
    //FCLASS
    //Outputs a number indicating the type of the operand
    //Encoded one hot
    logic[31:0] fclass_rd;
    always_comb begin
        fclass_rd = '0;
        fclass_rd[0] = args.rs1.d.sign & args.rs1_special_case.inf;
        fclass_rd[1] = args.rs1.d.sign & args.rs1_original_hidden_bit & ~|args.rs1_special_case;
        fclass_rd[2] = args.rs1.d.sign & ~args.rs1_original_hidden_bit & ~args.rs1_special_case.zero;
        fclass_rd[3] = args.rs1.d.sign & args.rs1_special_case.zero;
        fclass_rd[4] = ~args.rs1.d.sign & args.rs1_special_case.zero;
        fclass_rd[5] = ~args.rs1.d.sign & ~args.rs1_original_hidden_bit & ~args.rs1_special_case.zero;
        fclass_rd[6] = ~args.rs1.d.sign & args.rs1_original_hidden_bit & ~|args.rs1_special_case;
        fclass_rd[7] = ~args.rs1.d.sign & args.rs1_special_case.inf;
        fclass_rd[8] = args.rs1_special_case.snan;
        fclass_rd[9] = args.rs1_special_case.qnan;
    end

    ////////////////////////////////////////////////////
    //FCMP
    //Implements equal, less than, and less than or equal
    //For these instructions, +-0 are identical and flags can be raised for NaN operands
    logic[31:0] fcmp_rd;
    logic invalid_cmp;
    logic unordered;
    logic sign_eq;
    logic expo_eq;
    logic frac_eq;
    logic feq;
    logic flt;
    logic fle;

    //FLT/FLE are signalling (raise on NaN)
    assign invalid_cmp = (~args.rm[1] & (args.rs1_special_case.qnan | args.rs2_special_case.qnan)) | args.rs1_special_case.snan | args.rs2_special_case.snan;
    assign unordered = args.rs1_special_case.qnan | args.rs1_special_case.snan | args.rs2_special_case.qnan | args.rs2_special_case.snan;

    assign sign_eq = args.rs1.d.sign == args.rs2.d.sign;
    assign expo_eq = args.rs1.d.expo == args.rs2.d.expo;
    assign frac_eq = args.rs1.d.frac == args.rs2.d.frac;

    assign feq = (args.rs1_special_case.zero & args.rs2_special_case.zero) | (sign_eq & expo_eq & frac_eq);
    assign flt = sign_eq ? (args.swap ^ args.rs1.d.sign) & ~(sign_eq & expo_eq & frac_eq) : args.rs1.d.sign & ~(args.rs1_special_case.zero & args.rs2_special_case.zero);
    assign fle = flt | feq;

    always_comb begin
        fcmp_rd = '0;
        if (args.rm[1])
            fcmp_rd[0] = feq & ~unordered;
        else if (args.rm[0])
            fcmp_rd[0] = flt & ~unordered;
        else
            fcmp_rd[0] = fle & ~unordered;
    end


    //Choose between the three single cycle operations
    logic[31:0] single_rd;
    logic single_valid;
    logic single_invalid;
    always_ff @(posedge clk) begin
        if (issue.new_request) begin
            single_valid <= ~args.f2i;
            single_invalid <= args.fcmp & invalid_cmp;
            if (args.fcmp)
                single_rd <= fcmp_rd;
            else if (args.fclass)
                single_rd <= fclass_rd;
            else
                single_rd <= fmv_rd;
        end
    end


    ////////////////////////////////////////////////////
    //F2I
    //First cycle detects edge cases and shifts args
    //Second cycle rounds
    logic[2:0] grs;
    logic[FRAC_WIDTH:0] rs1_frac;
    logic[FRAC_WIDTH:0] f2i_frac;
    logic[31:0] f2i_int;
    logic[32+FRAC_WIDTH-1:0] shift_in;
    logic[32+FRAC_WIDTH-1:0] f2i_int_dot_frac;
    logic rs1_expo_unbiased_greater_than_31;
    logic rs1_expo_unbiased_greater_than_30;
    logic subtract;
    logic roundup;
    
    //Cycle 1 - calculate roundup and detect special and edge cases
    assign rs1_expo_unbiased_greater_than_31 = args.rs1.d.expo > (BIAS+31);
    assign rs1_expo_unbiased_greater_than_30 = args.rs1.d.expo > (BIAS+30);
    assign rs1_frac = {args.rs1_hidden, args.rs1.d.frac};
    assign shift_in = {{31{1'b0}}, rs1_frac};

    //Left shift according to exponent
    assign f2i_int_dot_frac = shift_in << args.rs1_expo_unbiased;
    always_comb begin
        if (args.int_less_than_1) begin
            f2i_int = '0;
            f2i_frac = rs1_frac;
        end else
            {f2i_int, f2i_frac} = {f2i_int_dot_frac, 1'b0};
    end

    //Calculate rounding bits and -roundup or +roundup
    logic sticky;
    assign sticky = |f2i_frac[FRAC_WIDTH-2:0];
    always_comb begin
        if (args.int_less_than_1) begin
            if (args.rs1.d.expo == expo_d_t'(BIAS-1))
                grs = {f2i_frac[FRAC_WIDTH-:2], sticky};
            else if (args.rs1.d.expo == expo_d_t'(BIAS-2))
                grs = {1'b0, f2i_frac[FRAC_WIDTH], f2i_frac[FRAC_WIDTH-1] | sticky};
            else
                grs = {2'b0, (|f2i_frac[FRAC_WIDTH-:2] | sticky)};
        end else
            grs = {f2i_frac[FRAC_WIDTH-:2], sticky};
    end

    fp_roundup f2i_int_roundup (
        .sign(args.rs1.d.sign),
        .rm(args.rm),
        .grs(grs),
        .lsb(f2i_int[0]),
        .roundup(roundup),
        .result_if_overflow()
    );

    assign subtract = args.rs1.d.sign & args.is_signed;

    //Special case handling - this is sometimes the critical path in the FPU
    //This special case detection can be done in the second cycle, which may make that a new critical path
    //However, calculating the roundup takes approximately the same amount of time as these special cases
    logic inexact;
    logic all_frac;
    logic greater_than_largest_unsigned_int;
    logic smaller_than_smallest_unsigned_int;
    logic greater_than_largest_signed_int;
    logic smaller_than_smallest_signed_int;
    logic special;
    assign inexact = |grs;
    assign all_frac = &f2i_int[30:0];

    assign greater_than_largest_unsigned_int = ~args.is_signed & (~args.rs1.d.sign | args.rs1_special_case.snan | args.rs1_special_case.qnan) & ((f2i_int[31] & all_frac & roundup) | rs1_expo_unbiased_greater_than_31);
    assign smaller_than_smallest_unsigned_int = ~args.is_signed & args.rs1.d.sign & ~args.rs1_special_case.zero & ~(args.int_less_than_1 & ~roundup);
    assign greater_than_largest_signed_int = args.is_signed & ((args.rs1_special_case.snan | args.rs1_special_case.qnan | ~args.rs1.d.sign) & ((~f2i_int[31] & all_frac & roundup) | rs1_expo_unbiased_greater_than_30));
    assign smaller_than_smallest_signed_int = args.is_signed & args.rs1.d.sign & ((f2i_int[31] & (|f2i_int[30:0] | roundup)) | rs1_expo_unbiased_greater_than_31);
    assign special = (~args.is_signed & (greater_than_largest_unsigned_int | smaller_than_smallest_unsigned_int)) | (args.is_signed & (greater_than_largest_signed_int | smaller_than_smallest_signed_int));


    //Cycle 2 - do the rounding and override special cases
    //Input negative -> -roundup - f2i_int
    //Input positive ->  roundup + f2i_int
    logic r_greater_than_largest_unsigned_int;
    logic r_greater_than_largest_signed_int;
    logic r_smaller_than_smallest_signed_int;
    logic r_inexact;
    logic r_special;
    logic r_subtract;
    logic r_roundup;
    logic[31:0] r_f2i_int;
    logic[31:0] in1;
    logic[31:0] in2;
    logic[31:0] f2i_int_rounded;
    logic[31:0] special_case_result;
    logic carry_in;
    assign in1 = r_subtract ? -(32'(r_roundup)) : 32'(r_roundup);
    assign in2 = r_f2i_int ^ {32{r_subtract}};
    assign {f2i_int_rounded, carry_in} = {in1, 1'b1} + {in2, r_subtract};

    always_comb begin
        if (r_greater_than_largest_unsigned_int)
            special_case_result = 32'hffffffff; //2^32 - 1;
        else if (r_greater_than_largest_signed_int)
            special_case_result = 32'h7fffffff; //2^31 - 1;
        else if (r_smaller_than_smallest_signed_int)
            special_case_result = 32'h80000000; //-2^31;
        else
            special_case_result = 0;
    end

    //F2I pipeline
    always_ff @ (posedge clk) begin
        if (issue.new_request) begin
            r_greater_than_largest_unsigned_int <= greater_than_largest_unsigned_int;
            r_greater_than_largest_signed_int <= greater_than_largest_signed_int;
            r_smaller_than_smallest_signed_int <= smaller_than_smallest_signed_int;
            r_inexact <= inexact;
            r_special <= special;
            r_f2i_int <= f2i_int;
            r_subtract <= subtract;
            r_roundup <= roundup;
        end
    end

    //Multiplex the outputs from f2i and the single cycle units
    always_comb begin
        fflags = '0;
        if (single_valid) begin
            wb.rd = single_rd;
            fflags.nv = single_invalid;
        end
        else begin
            wb.rd = r_special ? special_case_result : f2i_int_rounded;
            fflags.nv = r_special;
            fflags.nx = r_inexact & ~r_special;
        end
    end

endmodule
