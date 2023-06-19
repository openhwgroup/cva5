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


package fpu_types;
    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;

    //fpu support
    //TODO: FPU only has 1 writeback group, and $clog2(1) = 0
    //Need to force LOG2_FP_COMMIT_PORTS to 1
    localparam LOG2_FP_COMMIT_PORTS = 1; //$clog2(FP_NUM_WB_GROUPS);
    //localparam LOG2_MAX_IDS = $clog2(MAX_IDS);

    //typedef logic [LOG2_MAX_IDS-1:0] id_t;
    //Hardcoding fp_rs_wb_group_t width to 1
    //typedef logic [$clog2(FP_NUM_WB_GROUPS)-1:0] fp_rs_wb_group_t;
    typedef logic [GRS_WIDTH-1:0] grs_t;
    typedef logic [EXPO_WIDTH-1:0] fp_shift_amt_t;
    localparam HALF_GRS_WIDTH = GRS_WIDTH/2; // FMUL, FSQRT, FDIV

    //constants
    localparam BIAS = 2**(EXPO_WIDTH-1) - 1;
    localparam BIAS_F = 2**(EXPO_WIDTH_F-1)-1;
    localparam E_MIN = {{(EXPO_WIDTH-1){1'b0}}, 1'b1}; //min exponent represented in IEEE
    localparam E_MAX = {{(EXPO_WIDTH-1){1'b1}}, 1'b0};   //max exponent represented in IEEE
    localparam [FLEN-1:0] CANONICAL_NAN = {1'b0, {EXPO_WIDTH{1'b1}}, 1'b1, {(FRAC_WIDTH-1){1'b0}}}; //canonical NaN

    localparam [FLEN-1:0] SNAN = {1'b0, {EXPO_WIDTH{1'b1}}, 2'b01, {(FRAC_WIDTH-2){1'b0}}}; //signaling NaN
    localparam [FLEN-2:0] UNDERFLOW_DEFAULT_RESULT = {(FLEN-1){1'b0}};

    localparam FP_NUM_UNITS = 4;

    typedef struct packed{
        id_t id;
        logic [31:0] pc;
        logic [31:0] instruction;
        logic valid;
        fetch_metadata_t fetch_metadata;
        logic float_wb2_int_reg;
        logic is_float;
        logic accumulating_csrs;
    } fp_decode_packet_t;

    typedef struct packed{
        id_t id;
        logic valid;
        logic [FLEN-1:0] data;
        logic expo_overflow;
        logic [4:0] fflags;
        logic [2:0] rm;
        logic d2s;
        //shared with normalization
        logic carry;
        logic safe;
        logic hidden;
        logic [GRS_WIDTH-1:0] grs;
        fp_shift_amt_t clz;
        logic subnormal;
        logic right_shift;
        logic[EXPO_WIDTH-1:0] right_shift_amt;
    } fp_normalize_packet_t;

    typedef struct packed {
        logic valid;
        id_t   id;
        logic [4:0] fflags;
        logic [2:0] rm;
        logic d2s;
        logic sign_norm;
        logic [EXPO_WIDTH-1:0] expo_norm;
        logic expo_overflow_norm;
        logic right_shift;
        logic [EXPO_WIDTH-1:0] shift_amt;
        logic sp_overflow;
        logic [EXPO_WIDTH_F-1:0] sp_expo;
        logic signed [FRAC_WIDTH+3+GRS_WIDTH-1:0] shifter_in;
    } fp_normalize_pre_processing_packet_t;

    typedef struct packed{
        id_t id;
        logic valid;
        logic [FLEN-1:0] data;
        logic expo_overflow;
        logic hidden;
        logic roundup;
        logic [4:0] fflags;
        logic [FLEN-1:0] result_if_overflow;
        //logic [2:0] rm;
        logic d2s;
    } fp_round_packet_t;

    typedef struct packed{
        id_t id;
        logic valid;
        logic [FLEN-1:0] data;
    } fp_wb_packet_t;

    typedef struct packed{
        id_t id;
        logic done;
        logic [XLEN-1:0] rd;
        logic [4:0] fflags;
    } unit_writeback_t;

    typedef struct packed{
        id_t id;
        logic done;
        logic [FLEN-1:0] rd;
    } fp_unit_writeback_t;

    typedef struct packed{
        logic valid;
        id_t id;
        logic [4:0] fflags;
    } fflags_writeback_t;

    typedef struct packed {
      id_t id;
      logic wb2_float; //used to mux fflags tables
    } fcsr_fifo_data_t;

    typedef struct packed{
        id_t id;
        logic valid;
        phys_addr_t phys_addr;
        logic [FLEN-1:0] data;
    } fp_commit_packet_t;

    typedef struct packed{
        logic [2:0] rm;
        logic valid;
        logic [FP_NUM_UNITS-1:0] unit;
        logic [FLEN-1:0] rs1;
        logic [FLEN-1:0] rs2;
        logic [FLEN-1:0] rs3;
        logic [XLEN-1:0] int_rs1;
        id_t id;
        logic is_single;
        logic enable_prenorm;
        logic is_fma;
        logic is_fmul;
        logic is_fadd;
        logic is_div;
        logic is_sqrt;
        logic is_i2f;
        logic is_mv_f2i;
        logic is_s2d;
        logic is_d2s;
        logic is_minmax;
        logic is_sign_inj;
        logic is_f2i;
        logic is_mv_i2f;
        logic is_fcmp;
        logic is_class;
        logic add;
        logic conv_signed;
        logic [1:0] fma_op;
    } fp_pre_processing_packet_t;

    typedef struct packed{
        logic [FLEN-1:0]    rs1;
        logic [FLEN-1:0]    rs2;
        logic [2:0]         rm;
        logic [3:0]         rs1_special_case;
        logic [3:0]         rs2_special_case;
    } fp_mul_inputs_t;

    typedef struct packed {
        logic [FLEN-1:0]     rs1;
        logic [FLEN-1:0]     rs2;
        logic                rs1_hidden_bit;
        logic                rs1_expo_overflow;
        logic                rs2_hidden_bit;
        logic                rs1_safe_bit;
        logic                rs2_safe_bit;
        logic [2:0]          rm;
        logic [3:0]          rs1_special_case;
        logic [3:0]          rs2_special_case;
        logic                swap;
        logic                add;
        logic [EXPO_WIDTH:0] expo_diff;
        logic                single;
        grs_t                fp_add_grs;
    } fp_add_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]       rs1;
        logic [FLEN-1:0]       rs2;
        logic [FLEN-1:0]       rs3;

        logic [EXPO_WIDTH-1:0] rs1_pre_normalize_shift_amt;
        logic [EXPO_WIDTH-1:0] rs2_pre_normalize_shift_amt;
        logic                  rs1_subnormal;
        logic                  rs2_subnormal;
        logic                  rs3_subnormal;
        logic                  rs1_hidden_bit;
        logic                  rs2_hidden_bit;
        logic                  rs3_hidden_bit;

        logic [3:0]            rs1_special_case;
        logic [3:0]            rs2_special_case;
        logic [3:0]            rs3_special_case;

        logic [6:0]            op;         //only need 3rd and 4th bits (nfmadd)
        logic [2:0]            rm;
        logic [2:0]            instruction;     //support fused fadd fmul and fmadd unit {fmadd, fadd, fmul}

        fp_add_inputs_t        fp_add_inputs;
    } fp_madd_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]       rs1;
        logic [FLEN-1:0]       rs2;        //not needed for sqrt
        logic                  rs1_hidden_bit;
        logic                  rs2_hidden_bit;
        logic [EXPO_WIDTH-1:0] rs1_pre_normalize_shift_amt;
        logic [EXPO_WIDTH-1:0] rs2_pre_normalize_shift_amt;
        logic                  rs1_normal;
        logic                  rs2_normal;
        logic [2:0]            rm;
        id_t                   id;
        logic                  is_sqrt;
        logic [3:0]            rs1_special_case;
        logic [3:0]            rs2_special_case;
        logic                  single;
    } fp_div_sqrt_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]    rs1;
        logic [FLEN-1:0]    rs2;        //not needed for sqrt
        logic [6:0]         fn7;        //only need to two 2nd bit
        logic [2:0]         rm;
        id_t                id;
    } fp_div_inputs_t;

    typedef enum logic[2:0] {
        NEG_THREE = 3'b010, //Only reached by subtraction when last quotient digit is -2
        NEG_TWO = 3'b011,
        NEG_ONE = 3'b001,
        ZERO = 3'b000,
        POS_ONE = 3'b101,
        POS_TWO = 3'b111
    } q_t;

    typedef struct packed{
        logic [FLEN-1:0]    rs1;
        id_t                id;
    } fp_sqrt_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]    f2i_rs1;          //will be padded if input is integer
        logic               f2i_rs1_hidden;
        logic [3:0]         f2i_rs1_special_case;
        logic [XLEN-1:0]    i2f_rs1;
        logic [2:0]         rm;
        logic               is_mv;             //RV32 does not support FMV.D
        logic               is_signed;
        logic               is_float;
        logic               is_f2f;             //single <-> double
        logic               is_d2s;
    } fp_cvt_mv_inputs_t;

    typedef struct packed{
        logic [XLEN-1:0]    int_rs1_abs;
        logic               int_rs1_zero;
        logic               int_rs1_sign;
    } fp_i2f_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]    rs1;
        logic               invalid;
        logic               hidden;
    } fp_minmax_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]    rs1;
        logic               hidden;
    } fp_sign_inject_inputs_t;

    typedef struct packed{
        logic [31:0]        rs1;
    } fp_mv_i2f_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]    rs1;
        logic               invalid;
        logic               inexact;
        logic               hidden;
    } fp_conv_inputs_t;

    typedef struct packed{ //TODO: union inputs?
        fp_i2f_inputs_t         fp_i2f_inputs;
        fp_minmax_inputs_t      fp_minmax_inputs;
        fp_sign_inject_inputs_t fp_sign_inject_inputs;
        fp_mv_i2f_inputs_t      fp_mv_i2f_inputs;
        fp_conv_inputs_t        fp_conv_inputs;

        logic [4:0]         instruction; //{conv, mvi2f, i2f, minmax, sign_inj}
        logic [2:0]         rm;
        logic               single;
    } fp_wb2fp_misc_inputs_t;

    typedef struct packed{
        logic                       sign;
        logic [EXPO_WIDTH-1:0]      expo_unbiased;
        logic [FRAC_WIDTH:0]        frac;
        //logic [EXPO_WIDTH-1:0]      left_shift_amt;
        //logic [XLEN+FRAC_WIDTH:0]   f2i_int_dot_frac;
        logic                       f2i_int_less_than_1;
        logic [EXPO_WIDTH-1:0]      abs_expo_unbiased;
        logic                       expo_unbiased_greater_than_31;
        logic                       expo_unbiased_greater_than_30;
        logic                       is_signed;
        logic                       subtract;
        logic [2:0]                 rm;
        logic                       nan;
    } fp_f2i_inputs_t;

    typedef struct packed{
        logic               swap;
        logic [FLEN-1:0]    rs1;
        logic [FLEN-1:0]    rs2;
        logic [3:0]         rs1_special_case;
        logic [3:0]         rs2_special_case;
        logic [2:0]         rm;
    } fp_cmp_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]    rs1;
        logic               rs1_hidden_bit;
        logic [3:0]         rs1_special_case;
    } fp_class_inputs_t;

    typedef struct packed{
        logic [FLEN_F-1:0]    rs1;
    } fp_mv_f2i_inputs_t;

    typedef struct packed{ //TODO: union? sharing fields?
        fp_mv_f2i_inputs_t fp_mv_f2i_inputs;
        fp_f2i_inputs_t fp_f2i_inputs;
        fp_cmp_inputs_t fp_cmp_inputs;
        fp_class_inputs_t fp_class_inputs;

        logic [3:0]         instruction; //{mvf2i, f2i, cmp, class}
    } fp_wb2int_misc_inputs_t;

    //intermediate outputs from FMUL for FMADD instructions
    typedef struct packed {
        logic is_fma;
        fp_unit_writeback_t mul_wb;
        logic mul_wb_rd_expo_overflow;
        logic mul_wb_rd_hidden;
        logic mul_wb_rd_safe;
        grs_t mul_grs;
        logic mul_op, add_op;
        logic [FLEN-1:0] rs3;
        logic rs3_hidden_bit;
        logic [2:0] mul_rm;
        logic [3:0] rs1_special_case;
        logic [3:0] rs2_special_case;
        logic [EXPO_WIDTH:0] expo_diff;
        logic swap;
        logic single;
    } fma_mul_outputs_t;

    //additional inputs to support FP LS
    typedef struct packed {
        logic [FLEN-1:0] rs2;
        logic forwarded_store;
        id_t store_forward_id;
        logic is_float;
    } fp_load_store_inputs_t;

    typedef struct packed {
        //id_t id;
        logic is_float;
        logic we;
    } fp_lq_entry_t;

    typedef struct packed {
        //id_t id;
        logic forwarded_store;
        logic is_float;
        logic we;
    } fp_sq_entry_t;

    typedef struct packed {
       //Decode
       logic fp_instruction_issued_dec;
       logic fp_operand_stall;
       logic fp_unit_stall;
       logic fp_no_id_stall;
       logic fp_no_instruction_stall;
       logic fp_other_stall;
       logic fls_operand_stall;
       logic fmadd_operand_stall;
       logic fadd_operand_stall;
       logic fmul_operand_stall;
       logic fdiv_operand_stall;
       logic fsqrt_operand_stall;
       logic fcmp_operand_stall;
       logic fsign_inject_operand_stall;
       logic fclass_operand_stall;
       logic fcvt_operand_stall;

       //Instruction mix
       logic fp_load_op;
       logic fp_store_op;
       logic fp_fmadd_op;
       logic fp_add_op;
       logic fp_mul_op;
       logic fp_div_op;
       logic fp_sqrt_op;
       logic fp_cvt_op;
       logic fp_cmp_op;
       logic fp_minmax_op;
       logic fp_class_op;
       logic fp_sign_inject_op;

       //unit stall
       logic operand_stall_due_to_fls;
       logic operand_stall_due_to_fmadd;
       logic operand_stall_due_to_fdiv_sqrt;
       logic operand_stall_due_to_wb2fp;

       //writeback stall
       logic fmadd_wb_stall;
       logic fmul_wb_stall;
       logic fdiv_sqrt_wb_stall;
       logic wb2fp_wb_stall;

       logic fmadd_stall_due_to_fmadd;
       logic fmadd_operand_stall_rs1;
       logic fmadd_operand_stall_rs2;
       logic fmadd_operand_stall_rs3;
       logic fadd_operand_stall_rs1;
       logic fadd_operand_stall_rs2;
       logic fmul_operand_stall_rs1;
       logic fmul_operand_stall_rs2;
       logic fadd_stall_due_to_fmadd;

       logic rs1_subnormal;
       logic rs2_subnormal;
       logic rs3_subnormal;
       logic rd_subnormal;
       logic wb_round_overflow;
       logic roundup;
       logic overflowExp;
       logic underflowExp;
    } fp_taiga_trace_events_t;

    typedef struct packed {
        int in_flight_ids;
    } LargeSigTrace_t;

    typedef struct packed {
        fp_taiga_trace_events_t events;
        LargeSigTrace_t sigs;
    } fp_trace_outputs_t;

    //fflag tracking for FP units that writeback to integer reg
    typedef struct packed {
        logic [4:0] fflags;
        //id_t id;
    } unit_fflags_wb_t;

    typedef union packed {
        logic[FLEN-1:0] raw;
        struct packed {
            logic sign;
            logic[EXPO_WIDTH-1:0] expo;
            logic[FRAC_WIDTH-1:0] frac;
        } d;
        struct packed {
            logic[FLEN-FLEN_F-1:0] box;
            logic sign;
            logic[EXPO_WIDTH_F-1:0] expo;
            logic[FRAC_WIDTH_F-1:0] frac;
        } s;
    } fp_t;
endpackage
