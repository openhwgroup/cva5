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

module fp_wb2fp_misc

    import fpu_types::*;
    import cva5_config::*;

    (
        input fp_wb2fp_misc_inputs_t args,
        unit_issue_interface.unit issue,
        fp_intermediate_wb_interface.unit wb
    );

    ////////////////////////////////////////////////////
    //Implementation
    //Sign injections, min/max, s2d, d2s, i2f, and moves
    //Single cycle, sharing a writeback port
    assign issue.ready = wb.ack; //ACK functions as READY here
    assign wb.id = issue.id;
    assign wb.done = issue.new_request;
    assign wb.rm = args.rm; //Only used for i2f

    ////////////////////////////////////////////////////
    //FMV
    //Transfers bits unchanged from an INT register to an FP register, boxing them
    //In reduced precision, transfers the lower bits
    fp_t fmv_rd;
    assign fmv_rd.s.box = '1;
    assign {fmv_rd.s.sign, fmv_rd.s.expo, fmv_rd.s.frac} = args.int_rs[FLEN_F-1:0];

    ////////////////////////////////////////////////////
    //FS2D
    //The actual conversion is done in preprocessing
    //Can only raise on SNAN
    fp_t s2d_rd;
    assign s2d_rd = args.rs1;

    ////////////////////////////////////////////////////
    //FD2S
    //The actual conversion is done in postprocessing
    //Canonicalizes NaNs and can also raise on SNAN
    fp_t d2s_rd;
    assign d2s_rd.raw = args.rs1_special_case.snan | args.rs1_special_case.qnan ? CANONICAL_NAN : args.rs1.raw;

    ////////////////////////////////////////////////////
    //FSGN
    //Modifies the sign of the first operand
    //Does NOT canonicalize NaNs and does not raise any flags
    logic sgn_sign;
    logic rs1_sign;
    logic rs2_sign;
    fp_t sgn_rd;

    assign rs1_sign = args.fsgnj_single ? args.rs1_boxed & args.rs1.s.sign : args.rs1.d.sign;
    assign rs2_sign = args.fsgnj_single ? args.rs2_boxed & args.rs2.s.sign : args.rs2.d.sign;

    always_comb begin
        if (args.rm[1]) //JX
            sgn_sign = rs1_sign ^ rs2_sign;
        else if (args.rm[0]) //JN
            sgn_sign = ~rs2_sign;
        else //J
            sgn_sign = rs2_sign;

        if (args.fsgnj_single) begin
            sgn_rd.s.box = '1;
            sgn_rd.s.sign = sgn_sign;
            //If rs1 is unboxed it is treated as the canonical NaN
            if (args.rs1_boxed)
                sgn_rd.raw[FLEN_F-2:0] = args.rs1.raw[FLEN_F-2:0];
            else
                sgn_rd.raw[FLEN_F-2:0] = {{EXPO_WIDTH_F{1'b1}}, 1'b1, {FRAC_WIDTH_F-1{1'b0}}};
        end
        else begin
            sgn_rd.d.sign = sgn_sign;
            sgn_rd.d.expo = args.rs1.d.expo;
            sgn_rd.d.frac = args.rs1.d.frac;
        end
    end

    ////////////////////////////////////////////////////
    //FMIN/FMAX
    //Returns the larger/smaller argument
    //Canonicalizes NaNs and can raise invalid
    fp_t fminmax_rd;
    logic fminmax_hidden;
    logic rs1_nan;
    logic rs2_nan;

    assign rs1_nan = args.rs1_special_case.qnan | args.rs1_special_case.snan;
    assign rs2_nan = args.rs2_special_case.qnan | args.rs2_special_case.snan;

    //args.rm[0] = MAX, args.swap means rs2 > rs1
    always_comb begin
        case({rs1_nan, rs2_nan, args.rs1.d.sign, args.rs2.d.sign, args.rm[0], args.swap}) inside
            6'b11????: begin
                fminmax_rd = CANONICAL_NAN;
                fminmax_hidden = 1;
            end
            6'b01????,
            6'b00100?,
            6'b00011?,
            6'b000010,
            6'b000001,
            6'b001111,
            6'b001100: begin
                fminmax_rd = args.rs1;
                fminmax_hidden = ~args.rs1_special_case.zero;
            end
            default: begin
                fminmax_rd = args.rs2;
                fminmax_hidden = ~args.rs2_special_case.zero;
            end
        endcase
    end

    ////////////////////////////////////////////////////
    //I2F
    //Converts an integer to a FP number
    //The actual shifting is done in postprocessing
    fp_t i2f_rd;
    grs_t i2f_grs;
    logic[4:0] int_clz;
    fp_shift_amt_t i2f_clz;
    logic int_rs1_zero;

    clz #(.WIDTH(32)) clz_inst (
        .clz_input(args.int_rs_abs),
        .clz(int_clz),
        .zero(int_rs1_zero)
    );

    assign i2f_rd.d.sign = args.i2f_sign;
    always_comb begin
        if (int_rs1_zero) begin
            i2f_clz = '0;
            i2f_rd.d.expo = '0;
        end
        else begin
            i2f_clz = '0;
            i2f_clz[5:0] = int_clz + 1;
            i2f_rd.d.expo = BIAS+32;
        end
    end

    //When the mantissa shrinks sufficiently, the integer can no longer fit in the mantissa so it spills into the grs bits
    generate if (FRAC_WIDTH >= 32) begin : gen_int_fits
        always_comb begin
            i2f_grs = '0;
            i2f_rd.d.frac = '0;
            i2f_rd.d.frac[FRAC_WIDTH-1-:32] = args.int_rs_abs;
        end
    end else begin : gen_int_in_grs
        always_comb begin
            i2f_rd.d.frac[FRAC_WIDTH-1:0] = args.int_rs_abs[31-:FRAC_WIDTH];
            i2f_grs = '0;
            i2f_grs[GRS_WIDTH-1-:32-FRAC_WIDTH] = args.int_rs_abs[31-FRAC_WIDTH:0];
        end
    end endgenerate


    //Multiplex outputs of different units
    always_comb begin
        wb.expo_overflow = 0;
        wb.fflags = '0;
        wb.carry = 0;
        wb.safe = 0;
        wb.hidden = 0;
        wb.grs = '0;
        wb.clz = '0;
        wb.right_shift = 0;
        wb.right_shift_amt = 'x;
        wb.subnormal = 0;
        wb.ignore_max_expo = 1;
        wb.d2s = 0;

        if (args.fmv)
            wb.rd = fmv_rd;
        else if (args.d2s) begin
            wb.rd = d2s_rd;
            wb.hidden = args.rs1_hidden;
            wb.d2s = 1;
            wb.fflags.nv = args.rs1_special_case.snan;
        end
        else if (args.fsgnj) begin
            wb.hidden = 1;
            wb.rd = sgn_rd;
        end
        else if (args.fminmax) begin
            wb.rd = fminmax_rd;
            wb.hidden = fminmax_hidden;
            wb.fflags.nv = args.rs1_special_case.snan | args.rs2_special_case.snan;
            wb.d2s = args.single;
        end
        else if (args.i2f) begin
            wb.rd = i2f_rd;
            wb.grs = i2f_grs;
            wb.clz = i2f_clz;
            wb.d2s = args.single;
        end
        else begin
            wb.rd = s2d_rd;
            wb.hidden = args.rs1_hidden;
            wb.fflags.nv = args.rs1_special_case.snan;
        end
    end

endmodule
