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


package fpu_types;
    import cva5_config::*;
    import cva5_types::*;

    typedef logic[GRS_WIDTH-1:0] grs_t;
    typedef logic[EXPO_WIDTH-1:0] fp_shift_amt_t;

    //Constants
    localparam BIAS = 2**(EXPO_WIDTH-1) - 1;
    localparam BIAS_F = 2**(EXPO_WIDTH_F-1)-1;
    localparam [FLEN-1:0] CANONICAL_NAN = {1'b0, {EXPO_WIDTH{1'b1}}, 1'b1, {(FRAC_WIDTH-1){1'b0}}}; //canonical NaN

    typedef logic[EXPO_WIDTH-1:0] expo_d_t;
    typedef logic[EXPO_WIDTH_F-1:0] expo_s_t;
    typedef logic[FRAC_WIDTH-1:0] frac_d_t;
    
    typedef union packed {
        logic[FLEN-1:0] raw;
        struct packed {
            logic sign;
            expo_d_t expo;
            frac_d_t frac;
        } d;
        struct packed {
            logic[FLEN-FLEN_F-1:0] box;
            logic sign;
            expo_s_t expo;
            logic[FRAC_WIDTH_F-1:0] frac;
        } s;
    } fp_t;

    typedef struct packed {
        logic inf;
        logic snan;
        logic qnan;
        logic zero;
    } special_case_t;

    typedef logic[2:0] rm_t;

    typedef struct packed {
        logic nv;
        logic dz;
        logic of;
        logic uf;
        logic nx;
    } fflags_t;

    typedef struct packed {
        rm_t rm;
        logic valid;
        logic[4:0] unit;
        fp_t rs1;
        fp_t rs2;
        fp_t rs3;
        logic[31:0] int_rs1;
        id_t id;
        logic is_single;
        logic is_fma;
        logic is_fadd;
        logic is_i2f;
        logic is_d2s;
        logic is_minmax;
        logic is_sign_inj;
        logic is_sign_inj_single;
        logic is_f2i;
        logic is_mv_i2f;
        logic is_fcmp;
        logic is_class;
        logic add;
        logic neg_mul;
        logic conv_signed;
    } fp_preprocessing_packet_t;

    typedef struct packed {
        fp_t rs1;
        fp_t rs2;
        logic rs1_hidden;
        logic rs2_hidden;
        logic rs1_safe;
        logic rs2_safe;
        special_case_t rs1_special_case;
        special_case_t rs2_special_case;
        logic rs1_expo_overflow;
        logic[EXPO_WIDTH:0] expo_diff;
        logic add;
        logic swap;
        grs_t fp_add_grs;
        rm_t rm;
        logic single;
    } fp_add_inputs_t;

    typedef struct packed {
        special_case_t rs1_special_case;
        special_case_t rs2_special_case;
        logic rs1_hidden;
        logic rs2_hidden;
        fp_t rs1;
        fp_t rs2;
        rm_t rm;
        logic single;
        fp_shift_amt_t rs2_prenormalize_shift_amt;
    } fp_mul_inputs_t;

    typedef struct packed {
        logic mul_sign;
        logic add_sign;
        fp_t rs3;
        logic rs3_hidden;
        special_case_t rs3_special_case;
    } fp_fma_inputs_t;

    typedef struct packed {
        logic add;
        logic fma;
        //mul is implicit if others unset
        fp_add_inputs_t add_args;
        fp_fma_inputs_t fma_args;
        fp_mul_inputs_t mul_args;
    } fp_madd_inputs_t;

    typedef struct packed {
        fp_t rs1;
        fp_t rs2;
        rm_t rm;
        logic rs1_hidden;
        logic rs2_hidden;
        fp_shift_amt_t rs1_prenormalize_shift_amt;
        fp_shift_amt_t rs2_prenormalize_shift_amt;
        logic single;
        special_case_t rs1_special_case;
        special_case_t rs2_special_case;
    } fp_div_inputs_t;

    //Digit set for division
    typedef enum logic[2:0] {
        NEG_THREE = 3'b010, //Only reached by subtraction when last quotient digit is -2
        NEG_TWO = 3'b011,
        NEG_ONE = 3'b001,
        ZERO = 3'b000,
        POS_ONE = 3'b101,
        POS_TWO = 3'b111
    } q_t;

    typedef struct packed {
        fp_t rs1;
        logic rs1_hidden;
        special_case_t special_case;
        fp_shift_amt_t rs1_prenormalize_shift_amt;
        rm_t rm;
        logic single;
    } fp_sqrt_inputs_t;

    typedef struct packed {
        logic i2f;
        logic fminmax;
        logic fsgnj;
        logic fmv;
        logic d2s;
        //s2d is implicit if others unset

        //Used by FMV
        logic[31:0] int_rs;
        //Used by S2D, D2S
        logic rs1_hidden;
        special_case_t rs1_special_case;
        //Used by S2D, D2S, FSGNJ
        fp_t rs1;
        //Used by FSGNJ
        logic fsgnj_single;
        logic rs1_boxed;
        logic rs2_boxed;
        //Used by FSGNJ, FMINMAX
        logic swap;
        fp_t rs2;
        //Used by FSGNJ, FMINMAX, I2F
        logic single;
        rm_t rm;
        //Used by FMINMAX
        special_case_t rs2_special_case;
        //Used by I2F
        logic[31:0] int_rs_abs;
        logic i2f_sign;
    } fp_wb2fp_misc_inputs_t;

    typedef struct packed {
        logic fclass;
        logic fcmp;
        logic f2i;
        //fmv is implicit if others unset

        //Used by f2i
        logic int_less_than_1;
        expo_d_t rs1_expo_unbiased;
        //Used by fclass, fcmp, f2i
        fp_t rs1;
        //Used by fclass
        logic rs1_original_hidden_bit;
        //Used by fclass, fcmp
        special_case_t rs1_special_case;
        //Used by fcmp
        special_case_t rs2_special_case;
        fp_t rs2;
        logic swap;
        //Used by fcmp as fn3 and f2i as rounding
        rm_t rm;
        //Used by f2i
        logic rs1_hidden;
        logic is_signed;
    } fp_wb2int_misc_inputs_t;

endpackage
