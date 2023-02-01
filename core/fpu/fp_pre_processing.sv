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

module fp_pre_processing
    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    import fpu_types::*;

#(
    parameter FP_NUM_UNITS,
    parameter fp_unit_id_param_t FP_UNIT_IDS
)(
    input logic clk,
    input logic rst,
    unit_issue_interface.unit i_fp_unit_issue [FP_NUM_UNITS-1:0],
    unit_issue_interface.decode o_fp_unit_issue [FP_NUM_UNITS-1:0],

    //Unit Inputs
    input fp_pre_processing_packet_t  i_fp_pre_processing_packet,


    output logic                      issue_advance,
    output fp_madd_inputs_t           o_fp_madd_inputs,
    output fp_div_sqrt_inputs_t       o_fp_div_sqrt_inputs,
    output fp_wb2fp_misc_inputs_t     o_fp_wb2fp_misc_inputs,
    output fp_wb2int_misc_inputs_t    o_fp_wb2int_misc_inputs
);

    /////////////////////////////////////////////
    //Control Logic
    id_t id;
    logic possible_issue;
    logic pre_processing_valid;
    logic pre_processing_stage_valid;
    logic pre_processing_stage_ready;
    logic [FP_NUM_UNITS-1:0] issue_to;
    logic [FP_NUM_UNITS-1:0] r_issue_to_issue_stage;
    logic [FP_NUM_UNITS-1:0] unit_needed_pre_processing_stage;
    logic [FP_NUM_UNITS-1:0] pre_processing_ready;
    logic [FP_NUM_UNITS-1:0] ready;

    //preprocessing can accept new inputs if
    //1. no inputs is currently in preprocessing stage
    //2. data currently being preprocessed will propagate forward
    assign pre_processing_valid = pre_processing_stage_valid & |pre_processing_ready;
    assign pre_processing_stage_ready = ~pre_processing_stage_valid | (pre_processing_stage_valid & (~|unit_needed_pre_processing_stage | |pre_processing_ready));
    assign issue_advance = pre_processing_stage_ready;// & issue.stage_valid;

    assign pre_processing_ready = ready & unit_needed_pre_processing_stage;

    assign issue_to = {FP_NUM_UNITS{pre_processing_valid}} & r_issue_to_issue_stage;

    always_ff @ (posedge clk) begin
        if (pre_processing_stage_ready) begin
            pre_processing_stage_valid <= issue.stage_valid & issue.is_float & ~issue.is_fld;
            unit_needed_pre_processing_stage <= i_fp_pre_processing_packet.unit_needed_issue_stage;
            r_issue_to_issue_stage <= i_fp_pre_processing_packet.issue_to_issue_stage;
            id <= i_fp_pre_processing_packet.id;
            possible_issue <= i_fp_pre_processing_packet.possible_issue;
        end
    end

    /////////////////////////////////////////////
    //Issue interface passby
    generate for (genvar i = 0; i < FP_NUM_UNITS; i++) begin
        assign o_fp_unit_issue[i].possible_issue = possible_issue;
        assign o_fp_unit_issue[i].new_request = issue_to[i];
        assign o_fp_unit_issue[i].id = id;
    end
    endgenerate

    //Ready signals are always combinational
    generate
        for (genvar i = 0; i < FP_NUM_UNITS; i++) begin
            assign i_fp_unit_issue[i].ready = ready[i]; //for issue stage
            assign ready[i] = o_fp_unit_issue[i].ready;
        end
    endgenerate

    /////////////////////////////////////////////
    //Unpack
    logic [FLEN-1:0] rs1, rs2, rs3;
    logic [FLEN-1:0] r_rs1, r_rs2, r_rs3;
    logic [2:0] rm, r_rm;
    issue_packet_t issue;
    logic r_is_i2f, r_is_f2i, r_is_class, r_is_fcmp, r_is_minmax, r_is_sign_inj;
    logic [6:0] opcode, r_opcode;
    logic [6:0] fn7, r_fn7;
    id_t issue_id, r_issue_id;

    assign rs1 = i_fp_pre_processing_packet.rs1;
    assign rs2 = i_fp_pre_processing_packet.rs2;
    assign rs3 = i_fp_pre_processing_packet.rs3;
    assign rm = i_fp_pre_processing_packet.rm;
    assign issue = i_fp_pre_processing_packet.issue;
    assign opcode = issue.opcode;
    assign fn7 = issue.fn7;
    assign issue_id = issue.id;

    always_ff @ (posedge clk) begin
        if (pre_processing_stage_ready) begin
            r_rs1 <= rs1;
            r_rs2 <= rs2;
            r_rs3 <= rs3;
            r_rm  <= rm;
            r_opcode <= opcode;
            r_fn7 <= fn7;
            r_issue_id <= issue_id;

            r_is_i2f <= issue.is_i2f;
            r_is_f2i <= issue.is_f2i;
            r_is_class <= issue.is_class;
            r_is_fcmp <= issue.is_fcmp;
            r_is_minmax <= issue.is_minmax;
            r_is_sign_inj <= issue.is_sign_inj;
        end
    end

    /////////////////////////////////////////////
    //Special Case Detection
    logic is_inf[FP_REGFILE_READ_PORTS], r_is_inf[FP_REGFILE_READ_PORTS], is_inf_swapped[FP_REGFILE_READ_PORTS];
    logic is_SNaN[FP_REGFILE_READ_PORTS], r_is_SNaN[FP_REGFILE_READ_PORTS],is_SNaN_swapped[FP_REGFILE_READ_PORTS] ;
    logic is_QNaN[FP_REGFILE_READ_PORTS], r_is_QNaN[FP_REGFILE_READ_PORTS], is_QNaN_swapped[FP_REGFILE_READ_PORTS];
    logic is_zero[FP_REGFILE_READ_PORTS], r_is_zero[FP_REGFILE_READ_PORTS], is_zero_swapped[FP_REGFILE_READ_PORTS];
    logic hidden_bit[FP_REGFILE_READ_PORTS], r_hidden_bit[FP_REGFILE_READ_PORTS];
    logic is_subnormal[FP_REGFILE_READ_PORTS], r_is_subnormal[FP_REGFILE_READ_PORTS], is_subnormal_swapped[FP_REGFILE_READ_PORTS];;

    fp_special_case_detection #(.FRAC_W(FRAC_WIDTH), .EXPO_W(EXPO_WIDTH))
        rs1_special_case_detection (
        .data_in (rs1),
        .is_inf (is_inf[RS1]),
        .is_SNaN (is_SNaN[RS1]),
        .is_QNaN (is_QNaN[RS1]),
        .is_zero (is_zero[RS1]),
        .hidden (hidden_bit[RS1])
    );

    fp_special_case_detection #(.FRAC_W(FRAC_WIDTH), .EXPO_W(EXPO_WIDTH))
        rs2_special_case_detection (
        .data_in (rs2),
        .is_inf (is_inf[RS2]),
        .is_SNaN (is_SNaN[RS2]),
        .is_QNaN (is_QNaN[RS2]),
        .is_zero (is_zero[RS2]),
        .hidden (hidden_bit[RS2])
    );

    fp_special_case_detection #(.FRAC_W(FRAC_WIDTH), .EXPO_W(EXPO_WIDTH))
        rs3_special_case_detection (
        .data_in (rs3),
        .is_inf (is_inf[RS3]),
        .is_SNaN (is_SNaN[RS3]),
        .is_QNaN (is_QNaN[RS3]),
        .is_zero (is_zero[RS3]),
        .hidden (hidden_bit[RS3])
    );

    assign is_subnormal[RS1] = ~hidden_bit[RS1];
    assign is_subnormal[RS2] = ~hidden_bit[RS2];
    assign is_subnormal[RS3] = ~hidden_bit[RS3];

    for (genvar i = 0; i < FP_REGFILE_READ_PORTS; i++) begin
        always_ff @ (posedge clk) begin
            if (pre_processing_stage_ready) begin
                r_is_inf[i] <= is_inf[i];
                r_is_zero[i] <= is_zero[i];
                r_is_SNaN[i] <= is_SNaN[i];
                r_is_QNaN[i] <= is_QNaN[i];
                r_hidden_bit[i] <= hidden_bit[i];
                r_is_subnormal[i] <= is_subnormal[i];
            end
        end
    end

    /////////////////////////////////////////////
    //Swap calculation
    logic [EXPO_WIDTH:0] expo_diff, expo_diff_negate;
    logic [EXPO_WIDTH:0] r_expo_diff, r_expo_diff_negate;
    logic [EXPO_WIDTH:0] expo_diff_issued;
    logic swap, r_swap;

    //Issue cycle - calculate swap?
    assign swap = expo_diff[EXPO_WIDTH] ? 1 : |expo_diff[EXPO_WIDTH-1:0] ? 0 : rs1[0+:FRAC_WIDTH] < rs2[0+:FRAC_WIDTH];
    generate if (ENABLE_SUBNORMAL) begin
        assign expo_diff = (rs1[FLEN-2-:EXPO_WIDTH] + {{(EXPO_WIDTH-1){1'b0}}, ~hidden_bit[RS1]})-
                        (rs2[FLEN-2-:EXPO_WIDTH] + {{(EXPO_WIDTH-1){1'b0}}, ~hidden_bit[RS2]}); // subnormal expo is implicitly set to 1
        assign expo_diff_negate = (rs2[FLEN-2-:EXPO_WIDTH] + {{(EXPO_WIDTH-1){1'b0}}, ~hidden_bit[RS2]}) -
                                (rs1[FLEN-2-:EXPO_WIDTH] + {{(EXPO_WIDTH-1){1'b0}}, ~hidden_bit[RS1]});
    end else begin
        assign expo_diff = (rs1[FLEN-2-:EXPO_WIDTH]) - (rs2[FLEN-2-:EXPO_WIDTH]);
        assign expo_diff_negate = (rs2[FLEN-2-:EXPO_WIDTH]) - (rs1[FLEN-2-:EXPO_WIDTH]);
    end
    endgenerate

    //Cycle 1 - exponent diff
    assign expo_diff_issued = r_expo_diff[EXPO_WIDTH] ? r_expo_diff_negate : r_expo_diff;

    always_ff @ (posedge clk) begin
        if (pre_processing_stage_ready) begin
            r_expo_diff <= expo_diff;
            r_expo_diff_negate <= expo_diff_negate;
            r_swap <= swap;
        end
    end

    /////////////////////////////////////////////
    //Shared Pre-normalize and Swap
    logic pre_normalize_enable;
    logic [EXPO_WIDTH-1:0] rs1_pre_normalize_shift_amt, rs2_pre_normalize_shift_amt;
    logic [EXPO_WIDTH-1:0] r_rs1_pre_normalize_shift_amt, r_rs2_pre_normalize_shift_amt;
    logic [EXPO_WIDTH-1:0] rs1_pre_normalize_shift_amt_swapped, rs2_pre_normalize_shift_amt_swapped;
    logic rs1_hidden_bit_pre_normalized, rs2_hidden_bit_pre_normalized;
    logic r_rs1_hidden_bit_pre_normalized, r_rs2_hidden_bit_pre_normalized;
    logic rs1_hidden_bit_pre_normalized_swapped, rs2_hidden_bit_pre_normalized_swapped;
    logic [FRAC_WIDTH-1:0] rs1_frac_pre_normalized, rs2_frac_pre_normalized;
    logic [FRAC_WIDTH-1:0] r_rs1_frac_pre_normalized, r_rs2_frac_pre_normalized;

    logic [FLEN-1:0] rs1_pre_normalized, rs2_pre_normalized;
    logic [FLEN-1:0] rs1_pre_normalized_swapped, rs2_pre_normalized_swapped;

    //Issue cycle - pre normalize rs1 and rs2
    //Pre-normalize only enabled for fma/fmul and fdiv/fsqrt
    assign pre_normalize_enable = issue.enable_pre_normalize;

    pre_normalize #(.WIDTH(FRAC_WIDTH+1)) pre_normalize_rs1(
        .rs2(rs1),
        .rs2_hidden_bit(hidden_bit[RS1]),
        .enable(pre_normalize_enable),
        .pre_normalize_shift_amt (rs1_pre_normalize_shift_amt),
        .frac_normalized({rs1_hidden_bit_pre_normalized, rs1_frac_pre_normalized})
    );
    pre_normalize pre_normalize_rs2(
        .rs2(rs2),
        .rs2_hidden_bit(hidden_bit[RS2]),
        .enable(pre_normalize_enable),
        .pre_normalize_shift_amt (rs2_pre_normalize_shift_amt),
        .frac_normalized({rs2_hidden_bit_pre_normalized, rs2_frac_pre_normalized})
    );

    //Cycle 1 - swap
    always_comb begin
        rs1_pre_normalized = {r_rs1[FLEN-1], r_rs1[FLEN-2-:EXPO_WIDTH], r_rs1_frac_pre_normalized};
        rs2_pre_normalized = {r_rs2[FLEN-1], r_rs2[FLEN-2-:EXPO_WIDTH], r_rs2_frac_pre_normalized};

        if (r_swap) begin
        //pre normalized rs1 rs2
            {rs1_pre_normalized_swapped, rs2_pre_normalized_swapped} = {rs2_pre_normalized, rs1_pre_normalized};
            {rs1_hidden_bit_pre_normalized_swapped, rs2_hidden_bit_pre_normalized_swapped} = {r_rs2_hidden_bit_pre_normalized, r_rs1_hidden_bit_pre_normalized}; //prenormalized hidden
            {rs1_pre_normalize_shift_amt_swapped, rs2_pre_normalize_shift_amt_swapped} = {r_rs2_pre_normalize_shift_amt, r_rs1_pre_normalize_shift_amt};

            //special case and hidden bit swap
            {is_subnormal_swapped[RS1], is_subnormal_swapped[RS2]} = {r_is_subnormal[RS2], r_is_subnormal[RS1]};
            {is_inf_swapped[RS1], is_inf_swapped[RS2]} = {r_is_inf[RS2], r_is_inf[RS1]};
            {is_SNaN_swapped[RS1], is_SNaN_swapped[RS2]} = {r_is_SNaN[RS2], r_is_SNaN[RS1]};
            {is_QNaN_swapped[RS1], is_QNaN_swapped[RS2]} = {r_is_QNaN[RS2], r_is_QNaN[RS1]};
            {is_zero_swapped[RS1], is_zero_swapped[RS2]} = {r_is_zero[RS2], r_is_zero[RS1]};
        end else begin
            {rs1_pre_normalized_swapped, rs2_pre_normalized_swapped} = {rs1_pre_normalized, rs2_pre_normalized};
            {rs1_hidden_bit_pre_normalized_swapped, rs2_hidden_bit_pre_normalized_swapped} = {r_rs1_hidden_bit_pre_normalized, r_rs2_hidden_bit_pre_normalized};
            {rs1_pre_normalize_shift_amt_swapped, rs2_pre_normalize_shift_amt_swapped} = {r_rs1_pre_normalize_shift_amt, r_rs2_pre_normalize_shift_amt};

            {is_subnormal_swapped[RS1], is_subnormal_swapped[RS2]} = {r_is_subnormal[RS1], r_is_subnormal[RS2]};
            {is_inf_swapped[RS1], is_inf_swapped[RS2]} = {r_is_inf[RS1], r_is_inf[RS2]};
            {is_SNaN_swapped[RS1], is_SNaN_swapped[RS2]} = {r_is_SNaN[RS1], r_is_SNaN[RS2]};
            {is_QNaN_swapped[RS1], is_QNaN_swapped[RS2]} = {r_is_QNaN[RS1], r_is_QNaN[RS2]};
            {is_zero_swapped[RS1], is_zero_swapped[RS2]} = {r_is_zero[RS1], r_is_zero[RS2]};
        end
    end

    always_ff @ (posedge clk) begin
        if (pre_processing_stage_ready) begin
            r_rs1_pre_normalize_shift_amt <= rs1_pre_normalize_shift_amt;
            r_rs2_pre_normalize_shift_amt <= rs2_pre_normalize_shift_amt;

            r_rs1_hidden_bit_pre_normalized <= rs1_hidden_bit_pre_normalized;
            r_rs2_hidden_bit_pre_normalized <= rs2_hidden_bit_pre_normalized;

            r_rs1_frac_pre_normalized <= rs1_frac_pre_normalized;
            r_rs2_frac_pre_normalized <= rs2_frac_pre_normalized;
        end
    end

    /////////////////////////////////////////////
    //FMADD
    //Cycle Issue - decoding
    fp_add_inputs_t fp_add_inputs;
    logic is_fma, is_fadd, is_fmul;
    logic r_is_fma, r_is_fadd, r_is_fmul;
    logic add, r_add;

    assign is_fma = issue.opcode[6:4] == 3'b100; //Fused multiply and add instruction
    assign is_fmul = issue.opcode[6:4] == 3'b101 & issue.fn7[3];
    assign is_fadd = issue.opcode[6:4] == 3'b101 & ~issue.fn7[3];
    assign add = fn7 == FADD;

    //Cycle 1 - drive inputs
    assign o_fp_madd_inputs.instruction = {r_is_fma, r_is_fadd, r_is_fmul};
    assign o_fp_madd_inputs.rs1 = rs1_pre_normalized_swapped;
    assign o_fp_madd_inputs.rs2 = rs2_pre_normalized_swapped;
    assign o_fp_madd_inputs.rs1_pre_normalize_shift_amt = rs1_pre_normalize_shift_amt_swapped;
    assign o_fp_madd_inputs.rs2_pre_normalize_shift_amt = rs2_pre_normalize_shift_amt_swapped;
    assign o_fp_madd_inputs.rs3 = r_rs3;
    assign o_fp_madd_inputs.op = r_opcode;
    assign o_fp_madd_inputs.rm = r_rm;
    assign o_fp_madd_inputs.rs1_subnormal = is_subnormal_swapped[RS1];
    assign o_fp_madd_inputs.rs2_subnormal = is_subnormal_swapped[RS2];
    assign o_fp_madd_inputs.rs3_subnormal = r_is_subnormal[RS3];
    assign o_fp_madd_inputs.rs1_hidden_bit = rs1_hidden_bit_pre_normalized_swapped;
    assign o_fp_madd_inputs.rs2_hidden_bit = rs2_hidden_bit_pre_normalized_swapped;
    assign o_fp_madd_inputs.rs3_hidden_bit = r_hidden_bit[RS3];
    assign o_fp_madd_inputs.rs1_special_case = {is_inf_swapped[RS1], is_SNaN_swapped[RS1], is_QNaN_swapped[RS1], is_zero_swapped[RS1]};
    assign o_fp_madd_inputs.rs2_special_case = {is_inf_swapped[RS2], is_SNaN_swapped[RS2], is_QNaN_swapped[RS2], is_zero_swapped[RS2]};
    assign o_fp_madd_inputs.rs3_special_case = {r_is_inf[RS3], r_is_SNaN[RS3], r_is_QNaN[RS3], r_is_zero[RS3]};

    //Cycle 1 - separate packet for FADD
    //FADD inputs are not swapped during pre-processing
    assign o_fp_madd_inputs.fp_add_inputs = fp_add_inputs;
    assign fp_add_inputs.rs1 = r_rs1;
    assign fp_add_inputs.rs2 = r_rs2;
    assign fp_add_inputs.expo_diff = expo_diff_issued;
    assign fp_add_inputs.rs1_hidden_bit = r_hidden_bit[RS1];
    assign fp_add_inputs.rs2_hidden_bit = r_hidden_bit[RS2];
    assign fp_add_inputs.rs1_special_case = {r_is_inf[RS1], r_is_SNaN[RS1], r_is_QNaN[RS1], r_is_zero[RS1]};
    assign fp_add_inputs.rs2_special_case = {r_is_inf[RS2], r_is_SNaN[RS2], r_is_QNaN[RS2], r_is_zero[RS2]};
    assign fp_add_inputs.rm = r_rm;
    assign fp_add_inputs.fn7 = r_fn7;
    assign fp_add_inputs.swap = r_swap;
    assign fp_add_inputs.add = r_add;
    assign fp_add_inputs.rs1_expo_overflow = 0;
    assign fp_add_inputs.rs1_safe_bit = 0;
    assign fp_add_inputs.rs2_safe_bit = 0;
    assign fp_add_inputs.fp_add_grs = 0;

    always_ff @ (posedge clk) begin
        if (pre_processing_stage_ready) begin
            r_is_fma <= is_fma;
            r_is_fmul <= is_fmul;
            r_is_fadd <= is_fadd;
            r_add <= add;
        end
    end

    /////////////////////////////////////////////
    //FDIV/SQRT
    //Inputs are not swapped
    //Issue cycle
    //assign o_fp_div_sqrt_inputs.rs1 = {rs1[FLEN-1], rs1[FLEN-2-:EXPO_WIDTH], rs1_frac_pre_normalized};
    //assign o_fp_div_sqrt_inputs.rs2 = {rs2[FLEN-1], rs2[FLEN-2-:EXPO_WIDTH], rs2_frac_pre_normalized};
    //assign o_fp_div_sqrt_inputs.rs1_hidden_bit = rs1_hidden_bit_pre_normalized;
    //assign o_fp_div_sqrt_inputs.rs2_hidden_bit = rs2_hidden_bit_pre_normalized;
    //assign o_fp_div_sqrt_inputs.rs1_pre_normalize_shift_amt = rs1_pre_normalize_shift_amt;
    //assign o_fp_div_sqrt_inputs.rs2_pre_normalize_shift_amt = rs2_pre_normalize_shift_amt;
    //assign o_fp_div_sqrt_inputs.rm = rm;
    //assign o_fp_div_sqrt_inputs.fn7 = fn7;
    //assign o_fp_div_sqrt_inputs.id = issue_id;//fp_unit_issue[FP_DIV_SQRT_WB_ID].instruction_id;
    //assign o_fp_div_sqrt_inputs.rs1_special_case = {is_inf[RS1], is_SNaN[RS1], is_QNaN[RS1], is_zero[RS1]};
    //assign o_fp_div_sqrt_inputs.rs2_special_case = {is_inf[RS2], is_SNaN[RS2], is_QNaN[RS2], is_zero[RS2]};
    //assign o_fp_div_sqrt_inputs.rs1_normal = ~is_subnormal[RS1];
    //assign o_fp_div_sqrt_inputs.rs2_normal = ~is_subnormal[RS2];
    assign o_fp_div_sqrt_inputs.rs1 = rs1_pre_normalized;
    assign o_fp_div_sqrt_inputs.rs2 = rs2_pre_normalized;
    assign o_fp_div_sqrt_inputs.rs1_hidden_bit = r_rs1_hidden_bit_pre_normalized;
    assign o_fp_div_sqrt_inputs.rs2_hidden_bit = r_rs2_hidden_bit_pre_normalized;
    assign o_fp_div_sqrt_inputs.rs1_pre_normalize_shift_amt = r_rs1_pre_normalize_shift_amt;
    assign o_fp_div_sqrt_inputs.rs2_pre_normalize_shift_amt = r_rs2_pre_normalize_shift_amt;
    assign o_fp_div_sqrt_inputs.rm = r_rm;
    assign o_fp_div_sqrt_inputs.fn7 = r_fn7;
    assign o_fp_div_sqrt_inputs.id = r_issue_id;//fp_unit_issue[FP_DIV_SQRT_WB_ID].instruction_id;
    assign o_fp_div_sqrt_inputs.rs1_special_case = {r_is_inf[RS1], r_is_SNaN[RS1], r_is_QNaN[RS1], r_is_zero[RS1]};
    assign o_fp_div_sqrt_inputs.rs2_special_case = {r_is_inf[RS2], r_is_SNaN[RS2], r_is_QNaN[RS2], r_is_zero[RS2]};
    assign o_fp_div_sqrt_inputs.rs1_normal = ~r_is_subnormal[RS1];
    assign o_fp_div_sqrt_inputs.rs2_normal = ~r_is_subnormal[RS2];

    /////////////////////////////////////////////
    //WB2FP
    //i2f
    logic [XLEN-1:0] int_rs1, neg_int_rs1, abs_int_rs1;
    logic [XLEN-1:0] r_abs_int_rs1;
    logic int_rs1_sign, r_int_rs1_sign;
    logic i2f_is_signed, int_rs1_zero;
    logic r_int_rs1_zero;

    //minmax
    logic r_rs1_sign;
    logic r_is_max;  //the effective instruction executed
    logic r_output_swap;

    //Issue Cycle
    //i2f
    assign i2f_is_signed = ~issue.rs_addr[RS2][0];
    assign int_rs1 = i_fp_pre_processing_packet.int_rs1;
    assign neg_int_rs1 = -i_fp_pre_processing_packet.int_rs1;
    assign int_rs1_sign = i2f_is_signed & int_rs1[XLEN-1];
    assign abs_int_rs1 = (i2f_is_signed & int_rs1[XLEN-1]) ? neg_int_rs1 : int_rs1; //TODO compbien into one adder
    assign int_rs1_zero = ~|int_rs1;

    //Cycle 1 - instruction inputs
    assign o_fp_wb2fp_misc_inputs.instruction = {r_is_i2f, r_is_minmax, r_is_sign_inj};
    assign o_fp_wb2fp_misc_inputs.rm = r_rm;

    //minmax - |rs1_pre_normalizaed_swapped| > |rs2_pre_normalized_swapped|
    //if either one input is NaN, then rs1_pre_normalized_swapped = NaN
    assign r_rs1_sign = rs1_pre_normalized_swapped[FLEN-1];
    assign r_is_max = r_rm[0];
    always_comb begin
        if (r_is_SNaN[RS2] | r_is_QNaN[RS2] ^ r_is_SNaN[RS1] | r_is_QNaN[RS1])  //1 NaN input
            r_output_swap = 1;
        else if (r_is_SNaN[RS2] | r_is_QNaN[RS2] & r_is_SNaN[RS1] | r_is_QNaN[RS1]) //2 NaN inputs
            r_output_swap = 1;
        else
            r_output_swap = (~r_rs1_sign & ~r_is_max) | (r_rs1_sign & r_is_max);
    end
    assign o_fp_wb2fp_misc_inputs.fp_minmax_inputs.rs1 = r_output_swap ? rs2_pre_normalized_swapped : rs1_pre_normalized_swapped;
    assign o_fp_wb2fp_misc_inputs.fp_minmax_inputs.invalid = r_is_SNaN[RS1] | r_is_SNaN[RS2];
    assign o_fp_wb2fp_misc_inputs.fp_minmax_inputs.hidden = r_output_swap ? rs2_hidden_bit_pre_normalized_swapped : rs1_hidden_bit_pre_normalized_swapped;

    //i2f
    assign o_fp_wb2fp_misc_inputs.fp_i2f_inputs.int_rs1_abs = r_abs_int_rs1;
    assign o_fp_wb2fp_misc_inputs.fp_i2f_inputs.int_rs1_sign = r_int_rs1_sign;
    assign o_fp_wb2fp_misc_inputs.fp_i2f_inputs.int_rs1_zero = r_int_rs1_zero;

    //sign_inj
    always_comb begin
        case(r_rm)
            default: o_fp_wb2fp_misc_inputs.fp_sign_inject_inputs.rs1 = {r_rs2[FLEN-1], r_rs1[FLEN-2:0]};
            3'b001:  o_fp_wb2fp_misc_inputs.fp_sign_inject_inputs.rs1 = {~r_rs2[FLEN-1], r_rs1[FLEN-2:0]};
            3'b010:  o_fp_wb2fp_misc_inputs.fp_sign_inject_inputs.rs1 = {r_rs2[FLEN-1] ^ r_rs1[FLEN-1], r_rs1[FLEN-2:0]};
        endcase
        o_fp_wb2fp_misc_inputs.fp_sign_inject_inputs.hidden = r_rs1_hidden_bit_pre_normalized;
    end

    always_ff @ (posedge clk) begin
        if (pre_processing_stage_ready) begin
            r_abs_int_rs1 <= abs_int_rs1;
            r_int_rs1_sign <= int_rs1_sign;
            r_int_rs1_zero <= int_rs1_zero;
        end
    end

    /////////////////////////////////////////////
    //WB2INT
    //Issue cycle F2I
    logic f2i_is_signed, r_f2i_is_signed;
    logic [EXPO_WIDTH-1:0] rs1_expo, rs1_expo_unbiased, abs_rs1_expo_unbiased;
    logic [EXPO_WIDTH-1:0] r_rs1_expo_unbiased, r_abs_rs1_expo_unbiased;
    logic f2i_int_less_than_1, r_f2i_int_less_than_1;
    logic rs1_expo_unbiased_greater_than_31, rs1_expo_unbiased_greater_than_30;
    logic r_rs1_expo_unbiased_greater_than_31, r_rs1_expo_unbiased_greater_than_30;

    assign f2i_is_signed = ~issue.rs_addr[RS2][0];
    assign rs1_expo = rs1[FLEN-2-:EXPO_WIDTH];

    assign {f2i_int_less_than_1, rs1_expo_unbiased} = (rs1_expo - BIAS);
    assign abs_rs1_expo_unbiased = - rs1_expo_unbiased;
    assign rs1_expo_unbiased_greater_than_31 = rs1_expo > (BIAS + (XLEN - 1));
    assign rs1_expo_unbiased_greater_than_30 = rs1_expo > (BIAS + (XLEN - 2));

    //Cycle 1 - WB2INT
    assign o_fp_wb2int_misc_inputs.instruction = {r_is_f2i, r_is_fcmp, r_is_class};
    assign o_fp_wb2int_misc_inputs.rm = r_rm;

    //Cycle 1 - F2I
    assign o_fp_wb2int_misc_inputs.fp_f2i_inputs.sign = r_rs1[FLEN-1];
    assign o_fp_wb2int_misc_inputs.fp_f2i_inputs.expo_unbiased = r_rs1_expo_unbiased;// > 31 ? 31 : r_rs1_expo_unbiased;
    assign o_fp_wb2int_misc_inputs.fp_f2i_inputs.frac = {r_hidden_bit[RS1], r_rs1[0+:FRAC_WIDTH]};
    assign o_fp_wb2int_misc_inputs.fp_f2i_inputs.f2i_int_less_than_1 = r_f2i_int_less_than_1;
    assign o_fp_wb2int_misc_inputs.fp_f2i_inputs.abs_expo_unbiased = r_abs_rs1_expo_unbiased;
    assign o_fp_wb2int_misc_inputs.fp_f2i_inputs.expo_unbiased_greater_than_31 = r_rs1_expo_unbiased_greater_than_31;
    assign o_fp_wb2int_misc_inputs.fp_f2i_inputs.expo_unbiased_greater_than_30 = r_rs1_expo_unbiased_greater_than_30;
    assign o_fp_wb2int_misc_inputs.fp_f2i_inputs.is_signed = r_f2i_is_signed;
    assign o_fp_wb2int_misc_inputs.fp_f2i_inputs.subtract = r_rs1[FLEN-1] & r_f2i_is_signed;
    assign o_fp_wb2int_misc_inputs.fp_f2i_inputs.rm = r_rm;

    //Cycle 1 - FCMP
    assign o_fp_wb2int_misc_inputs.fp_cmp_inputs.swap = r_swap;
    assign o_fp_wb2int_misc_inputs.fp_cmp_inputs.rs1 = r_rs1;
    assign o_fp_wb2int_misc_inputs.fp_cmp_inputs.rs2 = r_rs2;
    assign o_fp_wb2int_misc_inputs.fp_cmp_inputs.rs1_special_case = {r_is_inf[RS1], r_is_SNaN[RS1], r_is_QNaN[RS1], r_is_zero[RS1]};
    assign o_fp_wb2int_misc_inputs.fp_cmp_inputs.rs2_special_case = {r_is_inf[RS2], r_is_SNaN[RS2], r_is_QNaN[RS2], r_is_zero[RS2]};
    assign o_fp_wb2int_misc_inputs.fp_cmp_inputs.rm = r_rm;

    //Cycle 1 - FCLASS
    assign o_fp_wb2int_misc_inputs.fp_class_inputs.rs1 = r_rs1;
    assign o_fp_wb2int_misc_inputs.fp_class_inputs.rs1_hidden_bit = r_hidden_bit[RS1];
    assign o_fp_wb2int_misc_inputs.fp_class_inputs.rs1_special_case = {r_is_inf[RS1], r_is_SNaN[RS1], r_is_QNaN[RS1], r_is_zero[RS1]};

    always_ff @ (posedge clk) begin
        if (pre_processing_stage_ready) begin
            r_rs1_expo_unbiased <= rs1_expo_unbiased;
            r_f2i_int_less_than_1 <= f2i_int_less_than_1;
            r_abs_rs1_expo_unbiased <= abs_rs1_expo_unbiased;
            r_rs1_expo_unbiased_greater_than_31 <= rs1_expo_unbiased_greater_than_31;
            r_rs1_expo_unbiased_greater_than_30 <= rs1_expo_unbiased_greater_than_30;
            r_f2i_is_signed <= f2i_is_signed;
        end
    end

endmodule
