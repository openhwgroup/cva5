/*
 * Copyright © 2017-2020 Eric Matthews,  Lesley Shannon
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
 *             Yuhui Gao <yuhiug@sfu.ca>
 *             */


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
    typedef logic fp_rs_wb_group_t;
    //typedef logic [FRAC_WIDTH-1:0] grs_t;
    typedef logic [2:0] grs_t;
    localparam GRS_WIDTH = $bits(grs_t);
    typedef logic [EXPO_WIDTH-1:0] fp_shift_amt_t;

    //constants
    localparam BIAS = 2**(EXPO_WIDTH-1) - 1;
    localparam E_MIN = {{(EXPO_WIDTH-1){1'b0}}, 1'b1}; //min exponent represented in IEEE
    localparam E_MAX = {{(EXPO_WIDTH-1){1'b1}}, 1'b0};   //max exponent represented in IEEE
    localparam [FLEN-1:0] CANONICAL_NAN = {1'b0, {EXPO_WIDTH{1'b1}}, 1'b1, {(FRAC_WIDTH-1){1'b0}}}; //canonical NaN

    localparam [FLEN-1:0] SNAN = {1'b0, {EXPO_WIDTH{1'b1}}, 2'b01, {(FRAC_WIDTH-2){1'b0}}}; //signaling NaN
    localparam [FLEN-2:0] UNDERFLOW_DEFAULT_RESULT = {(FLEN-1){1'b0}};
   
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
        logic [31:0] pc;
        logic [31:0] instruction;
        logic [2:0] fn3;
        logic [6:0] fn7;
        logic [6:0] opcode;

        rs_addr_t [FP_REGFILE_READ_PORTS-1:0] rs_addr;
        phys_addr_t [FP_REGFILE_READ_PORTS-1:0] phys_rs_addr;
        //logic [$clog2(EXAMPLE_CONFIG.FP.FP_NUM_WB_GROUPS)-1:0] [FP_REGFILE_READ_PORTS-1:0] rs_wb_group;
        logic [FP_REGFILE_READ_PORTS-1:0] rs_wb_group;

        rs_addr_t rd_addr;
        phys_addr_t phys_rd_addr;
        //logic [$clog2(EXAMPLE_CONFIG.FP.FP_NUM_WB_GROUPS)-1:0] rd_wb_group;
        logic rd_wb_group;

        logic uses_int_rs1;
        logic uses_rs1;
        logic uses_rs2;
        logic uses_rs3;
        logic uses_rd;
        id_t id;
        logic stage_valid;
        logic float_wb2_int_reg;
        fetch_metadata_t fetch_metadata;
        logic is_float;
        logic accumulating_csrs;
    } fp_issue_packet_t;

    typedef struct packed{
        id_t id;
        logic valid;
        logic [FLEN-1:0] data;
        logic expo_overflow;
        logic [4:0] fflags;
        logic [2:0] rm;
        //shared with normalization
        logic carry;
        logic safe;
        logic hidden;
        logic [2:0] grs;
        fp_shift_amt_t clz;
        logic subnormal;
        logic right_shift;
        logic[EXPO_WIDTH-1:0] right_shift_amt;
    } fp_normalize_packet_t; 

    typedef struct packed{
        id_t id;
        logic valid;
        logic [FLEN-1:0] data;
        logic expo_overflow;
        logic hidden;
        logic [FLEN-1:0] result_if_overflow;
        logic roundup;
        logic [4:0] fflags;
        //logic [2:0] rm;
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
        logic [4:0] fflags;
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
        logic [FLEN-1:0]    rs1;
        logic [FLEN-1:0]    rs2;
        logic [2:0]         rm;
        logic [3:0]         rs1_special_case; 
        logic [3:0]         rs2_special_case; 
    } fp_mul_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]    rs1;
        logic [FLEN-1:0]    rs2;
        logic [FLEN-1:0]    rs3;
        logic [3:0]         rs1_special_case;
        logic [3:0]         rs2_special_case;
        logic [3:0]         rs3_special_case;
        logic [6:0]         op;         //only need 3rd and 4th bits (nfmadd)
        logic [2:0]         rm;     
        logic [2:0]         instruction;     //support fused fadd fmul and fmadd unit {fmadd, fadd, fmul}
        logic [6:0]         fn7;
        logic               rs1_hidden_bit; 
        logic               rs2_hidden_bit; 
        logic               rs3_hidden_bit; 
    } fp_madd_inputs_t;

    typedef struct packed {
        logic [FLEN-1:0]    rs1;
        logic [FLEN-1:0]    rs2;
        logic               rs1_hidden_bit;
        logic               rs2_hidden_bit;
        logic               rs1_safe_bit;
        logic               rs2_safe_bit;
        logic [2:0]         rm;
        logic [6:0]         fn7;
        logic [3:0]         rs1_special_case; 
        logic [3:0]         rs2_special_case; 
    } fp_add_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]    rs1;
        logic [FLEN-1:0]    rs2;        //not needed for sqrt
        logic               rs1_hidden_bit;
        logic               rs2_hidden_bit;        
        logic [6:0]         fn7;        //only need to two 2nd bit
        logic [2:0]         rm;
        id_t                id;
        logic               is_div;
        logic [3:0]         rs1_special_case;
        logic [3:0]         rs2_special_case;
    } fp_div_sqrt_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]    rs1;
        logic [FLEN-1:0]    rs2;        //not needed for sqrt
        logic [6:0]         fn7;        //only need to two 2nd bit
        logic [2:0]         rm;
        id_t                id;
    } fp_div_inputs_t;

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
        logic [XLEN-1:0]    i2f_rs1;
        logic [2:0]         rm;
        logic               is_signed;
    } fp_i2f_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]    rs1;
        logic [FLEN-1:0]    rs2;
        logic               rs1_hidden_bit;
        logic               rs2_hidden_bit;
        logic [3:0]         rs1_special_case;
        logic [3:0]         rs2_special_case;
        logic [2:0]         rm;
    } fp_minmax_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]    rs1;
        logic               rs1_hidden_bit;
        logic               rs2_sign;
        logic [2:0]         rm;
    } fp_sign_inject_inputs_t;

    typedef struct packed{
        logic [2:0]         instruction; //{i2f, minmax, sign_inj}
        logic [FLEN-1:0]    rs1;
        logic [XLEN-1:0]    int_rs1;
        logic [FLEN-1:0]    rs2;
        logic               rs1_hidden_bit;
        logic               rs2_hidden_bit;
        logic [3:0]         rs1_special_case;
        logic [3:0]         rs2_special_case;
        logic [2:0]         rm;
        logic               is_signed;
    } fp_wb2fp_misc_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]    f2i_rs1;          //will be padded if input is integer
        logic               f2i_rs1_hidden;
        logic [3:0]         f2i_rs1_special_case;
        logic [2:0]         rm;
        logic               is_signed;
    } fp_f2i_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]    rs1;
        logic [FLEN-1:0]    rs2;
        logic               rs1_hidden_bit;
        logic               rs2_hidden_bit;
        logic [2:0]         rm;        //only need lower 2 bits
        logic [6:0]         fn7;        //min max or cmp select
        logic               is_sign_inj;
        logic               is_class;
        logic [3:0]         rs1_special_case;
        logic [3:0]         rs2_special_case;
    } fp_cmp_inputs_t;

    typedef struct packed{
        logic [FLEN-1:0]    rs1;
        logic               rs1_hidden_bit;
        logic [3:0]         rs1_special_case;
    } fp_class_inputs_t;

    typedef struct packed{
        logic [2:0]         instruction; //{f2i, cmp, class}
        logic [FLEN-1:0]    rs1;
        logic [FLEN-1:0]    rs2;
        logic               rs1_hidden_bit;
        logic               rs2_hidden_bit;
        logic [3:0]         rs1_special_case;
        logic [3:0]         rs2_special_case;
        logic [2:0]         rm;
        logic               is_signed;
    } fp_wb2int_misc_inputs_t;

    //intermediate outputs from FMUL for FMADD instructions
    typedef struct packed {
      logic is_fma;
      fp_unit_writeback_t mul_wb;
      logic mul_wb_rd_hidden;
      logic mul_wb_rd_safe;
      grs_t mul_grs;
      logic mul_op, add_op;
      logic [FLEN-1:0] rs3;
      logic rs3_hidden_bit;
      logic [2:0] mul_rm;
      logic [2:0] instruction;
      logic invalid_operation;
      logic [3:0] rs1_special_case;
      logic [3:0] rs2_special_case;
      logic [EXPO_WIDTH:0] expo_diff;
      logic swap;
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

    //typedef struct packed {
        //logic int_rs1_conflict;
        //logic [XLEN-1:0] int_rs1_data;
        //logic fp_rs1_conflict;
        //logic [FLEN-1:0] fp_rs1_data;
    //} shared_decode_t;

    typedef struct packed {
        //Decode
        logic fp_operand_stall;
        logic fp_unit_stall;
        logic fp_no_id_stall;
        logic fp_no_instruction_stall;
        logic fp_other_stall;
        logic fdiv_operand_stall;
        logic fmadd_operand_stall;
        logic fcmp_operand_stall;
        logic fsign_inject_operand_stall;
        logic fclass_operand_stall;
        logic fcvt_operand_stall;

        //Instruction mix
        logic fp_fmadd_op;
        logic fp_add_op;
        logic fp_mul_op;
        logic fp_div_op;
        logic fp_sqrt_op;
        logic fp_cvt_op;
        logic fp_cmp_op;
        logic fp_minmax_op;
        logic fp_class_op;

        //Register File
        logic rs1_forwarding_needed;
        logic rs2_forwarding_needed;
        logic rs1_and_rs2_forwarding_needed;

        //Writeback
        id_t num_instructions_in_flight;
        id_t num_of_instructions_pending_writeback;
    } fp_taiga_trace_events_t;

    typedef struct packed {
        taiga_trace_events_t events;
    } fp_trace_outputs_t;

    //fflag tracking for FP units that writeback to integer reg
    typedef struct packed {
      logic [4:0] fflags;
      //id_t id;
    } unit_fflags_wb_t;
endpackage


