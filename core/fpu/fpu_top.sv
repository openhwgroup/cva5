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
 
 module fpu_top
    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    import fpu_types::*;
    import opcodes::*;

    #(
        parameter FP_NUM_UNITS = 4,
        parameter fp_unit_id_param_t FP_UNIT_IDS,
        parameter FP_NUM_INTERMEDIATE_WB,
        parameter fp_wb_norm_round_param_t FP_NORM_ROUND_WB_IDS
    )
    (
        input logic clk,
        input logic rst,

        input decode_packet_t decode_stage,
        output logic unit_needed,
        output logic [REGFILE_READ_PORTS-1:0] uses_rs,
        output logic [FP_REGFILE_READ_PORTS-1:0] fp_uses_rs,
        output logic uses_rd,
        output logic fp_uses_rd,
        
        input issue_packet_t issue_stage,
        input logic issue_stage_ready,
        input logic [2:0] dyn_rm,
        input logic [31:0] int_rf [REGFILE_READ_PORTS],
        input logic [FLEN-1:0] fp_rf [FP_REGFILE_READ_PORTS],

        unit_issue_interface.unit issue,
        unit_writeback_interface.unit int_wb,
        fp_unit_writeback_interface.unit fp_wb
    );

    logic [FP_NUM_UNITS-1:0] internal_unit_needed;
    fp_madd_inputs_t madd_inputs;
    fp_div_sqrt_inputs_t div_sqrt_inputs;
    fp_wb2fp_misc_inputs_t wb2fp_inputs;
    fp_wb2int_misc_inputs_t wb2int_inputs;
    unit_issue_interface intermediate_issue [FP_NUM_UNITS-1:0] ();
    fp_intermediate_wb_interface intermediate_unit_wb [FP_NUM_INTERMEDIATE_WB] ();
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Decode
    always_comb begin
        uses_rs = '0;
        uses_rs[RS1] = decode_stage.instruction inside {
            FCVT_S_W, FCVT_S_WU, FMV_W_X,
            FCVT_D_W, FCVT_D_WU
        };

        fp_uses_rs = '0;
        fp_uses_rs[RS1] = decode_stage.instruction inside {
            FMADD_S, FMSUB_S, FNMSUB_S, FMMADD_S, FADD_S, FSUB_S, FMUL_S,
            FDIV_S, FSQRT_S, FSGNJ_S, FSGNJN_S, FSGNJX_S, FMIN_S, FMAX_S,
            FCVT_W_S, FCVT_WU_S, FMV_X_W, FEQ_S, FLT_S, FLE_S, FCLASS_S,
            FMADD_D, FMSUB_D, FNMSUB_D, FNMADD_D, FADD_D, FSUB_D, FMUL_D,
            FDIV_D, FSQRT_D, FSGNJ_D, FSGNJN_D, FSGNJX_D, FMIN_D, FMAX_D,
            FCVT_S_D, FCVT_D_S, FEQ_D, FLT_D, FLE_D, FCLASS_D, FCVT_W_D, FCVT_WU_D
        };
        fp_uses_rs[RS2] = decode_stage.instruction inside {
            FMADD_S, FMSUB_S, FNMSUB_S, FMMADD_S, FADD_S, FSUB_S, FMUL_S,
            FDIV_S, FSQRT_S, FSGNJ_S, FSGNJN_S, FSGNJX_S, FMIN_S, FMAX_S,
            FEQ_S, FLT_S, FLE_S,
            FMADD_D, FMSUB_D, FNMSUB_D, FNMADD_D, FADD_D, FSUB_D, FMUL_D,
            FDIV_D, FSQRT_D, FSGNJ_D, FSGNJN_D, FSGNJX_D, FMIN_D, FMAX_D,
            FEQ_D, FLT_D, FLE_D
        };
        fp_uses_rs[RS3] = decode_stage.instruction inside {
            FMADD_S, FMSUB_S, FNMSUB_S, FMMADD_S,
            FMADD_D, FMSUB_D, FNMSUB_D, FNMADD_D
        };

        uses_rd = decode_stage.instruction inside {
            FCVT_W_S, FCVT_WU_S, FMV_X_W, FEQ_S, FLT_S, FLE_S, FCLASS_S,
            FEQ_D, FLT_D, FLE_D, FCLASS_D, FCVT_W_D, FCVT_WU_D
        };
        fp_uses_rd = decode_stage.instruction inside {
            FMADD_S, FMSUB_S, FNMSUB_S, FMMADD_S, FADD_S, FSUB_S, FMUL_S,
            FDIV_S, FSQRT_S, FSGNJ_S, FSGNJN_S, FSGNJX_S, FMIN_S, FMAX_S,
            FCVT_S_W, FCVT_S_WU, FMV_W_X,
            FMADD_D, FMSUB_D, FNMSUB_D, FNMADD_D, FADD_D, FSUB_D, FMUL_D,
            FDIV_D, FSQRT_D, FSGNJ_D, FSGNJN_D, FSGNJX_D, FMIN_D, FMAX_D,
            FCVT_S_D, FCVT_D_S, FCVT_D_W, FCVT_D_WU
        };

        unit_needed = decode_stage.instruction inside {
            FMADD_S, FMSUB_S, FNMSUB_S, FMMADD_S, FADD_S, FSUB_S, FMUL_S,
            FMADD_D, FMSUB_D, FNMSUB_D, FNMADD_D, FADD_D, FSUB_D, FMUL_D,
            FDIV_S, FSQRT_S,
            FDIV_D, FSQRT_D,
            FSGNJ_S, FSGNJN_S, FSGNJX_S, FMIN_S, FMAX_S, FCVT_S_W, FCVT_S_WU, FMV_W_X,
            FSGNJ_D, FSGNJN_D, FSGNJX_D, FMIN_D, FMAX_D, FCVT_S_D, FCVT_D_S, FCVT_D_W, FCVT_D_WU,
            FCVT_W_S, FCVT_WU_S, FMV_X_W, FEQ_S, FLT_S, FLE_S, FCLASS_S,
            FEQ_D, FLT_D, FLE_D, FCLASS_D, FCVT_W_D, FCVT_WU_D
        };
    end

    ////////////////////////////////////////////////////
    //Shared preprocessing
    logic is_single;
    logic enable_prenorm; //TODO: required for conv instructions?
    //Instruction families
    logic is_fma;
    logic is_fmul;
    logic is_fadd;
    logic is_div;
    logic is_sqrt;
    logic is_i2f;
    logic is_mv_i2f;
    logic is_s2d;
    logic is_d2s;
    logic is_minmax;
    logic is_sign_inj;
    logic is_f2i;
    logic is_mv_f2i;
    logic is_fcmp;
    logic is_class;
    //Used to distinguish between instructions in a family
    logic add;
    logic conv_signed;
    logic[1:0] fma_op;
    logic[2:0] rm;

    fp_pre_processing_packet_t pkt;
    assign pkt.valid = issue.new_request;
    assign pkt.unit[FP_UNIT_IDS.FMADD] = is_fma | is_fmul | is_fadd;
    assign pkt.unit[FP_UNIT_IDS.FDIV_SQRT] = is_div | is_sqrt;
    assign pkt.unit[FP_UNIT_IDS.MISC_WB2FP] = is_i2f | is_mv_i2f | is_minmax | is_sign_inj | is_s2d | is_d2s;
    assign pkt.unit[FP_UNIT_IDS.MISC_WB2INT] = is_f2i | is_mv_f2i | is_fcmp | is_class;
    assign pkt.rs1 = fp_rf[RS1];
    assign pkt.rs2 = fp_rf[RS2];
    assign pkt.rs3 = fp_rf[RS3];
    assign pkt.int_rs1 = int_rf[RS1];
    assign pkt.id = issue.id;
    assign pkt.is_single = is_single;
    assign pkt.enable_prenorm = enable_prenorm;
    assign pkt.is_fma = is_fma;
    assign pkt.is_fmul = is_fmul;
    assign pkt.is_fadd = is_fadd;
    assign pkt.is_div = is_div;
    assign pkt.is_sqrt = is_sqrt;
    assign pkt.is_i2f = is_i2f;
    assign pkt.is_mv_f2i = is_mv_f2i;
    assign pkt.is_s2d = is_s2d;
    assign pkt.is_d2s = is_d2s;
    assign pkt.is_minmax = is_minmax;
    assign pkt.is_sign_inj = is_sign_inj;
    assign pkt.is_f2i = is_f2i;
    assign pkt.is_mv_i2f = is_mv_i2f;
    assign pkt.is_fcmp = is_fcmp;
    assign pkt.is_class = is_class;
    assign pkt.add = add;
    assign pkt.conv_signed = conv_signed;
    assign pkt.fma_op = fma_op;
    assign pkt.rm = rm;

    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            is_single <= issue_stage.instruction[25];
            enable_prenorm <= issue_stage.instruction inside {FMADD_D, FMSUB_D, FNMSUB_D, FMMADD_D, FMUL_D, FDIV_D, FSQRT_D, FCVT_W_D, FCVT_WU_D};
            is_fma <= issue_stage.instruction inside {FMADD_S, FMSUB_S, FNMSUB_S, FMMADD_S, FMADD_D, FMSUB_D, FNMSUB_D, FNMADD_D};
            is_fmul <= issue_stage.instruction inside {FMUL_S, FMUL_D};
            is_fadd <= issue_stage.instruction inside {FADD_S, FSUB_S, FADD_D, FSUB_D};
            is_div <= issue_stage.instruction inside {FDIV_S, FDIV_D};
            is_sqrt <= issue_stage.instruction inside {FSQRT_S, FSQRT_D};
            is_i2f <= issue_stage.instruction inside {FCVT_S_W, FCVT_S_WU, FCVT_D_W, FCVT_D_WU};
            is_mv_f2i <= issue_stage.instruction == FMV_X_W;
            is_s2d <= issue_stage.instruction == FCVT_D_S;
            is_d2s <= issue_stage.instruction == FCVT_S_D;
            is_minmax <= issue_stage.instruction inside {FMIN_S, FMAX_S, FMIN_D, FMAX_D};
            is_sign_inj <= issue_stage.instruction inside {FSGNJ_S, FSGNJN_S, FSGNJX_S, FSGNJ_D, FSGNJN_D, FSGNJX_D};
            is_f2i <= issue_stage.instruction inside {FCVT_W_S, FCVT_WU_S, FCVT_W_D, FCVT_WU_D};
            is_mv_i2f <= issue_stage.instruction == FMV_W_X;
            is_fcmp <= issue_stage.instruction inside {FEQ_S, FLT_S, FLE_S, FEQ_D, FLT_D, FLE_D};
            is_class <= issue_stage.instruction inside {FCLASS_S, FCLASS_D};
            add <= ~|issue_stage.instruction[31:25];
            conv_signed <= ~issue_stage.instruction[20];
            fma_op <= issue_stage.instruction[3:2];
            rm <= &issue_stage.instruction[14:12] ? dyn_rm : issue_stage.instruction[14:12];
        end
    end

    fp_pre_processing #(.FP_NUM_UNITS(FP_NUM_UNITS)) fp_pre_processing_inst (
        .clk(clk),
        .rst(rst),
        .o_fp_unit_issue(intermediate_issue),
        .i_fp_pre_processing_packet(pkt),
        .ready(issue.ready),
        .o_fp_madd_inputs(madd_inputs),
        .o_fp_div_sqrt_inputs(div_sqrt_inputs),
        .o_fp_wb2fp_misc_inputs(wb2fp_inputs),
        .o_fp_wb2int_misc_inputs(wb2int_inputs)
    );


    ////////////////////////////////////////////////////
    //Execution Units
    fp_madd_fused_top fp_madd_inst (
        .clk(clk),
        .rst(rst),
        .fp_madd_inputs(madd_inputs),
        .issue(intermediate_issue[FP_UNIT_IDS.FMADD]), 
        .fp_madd_wb(intermediate_unit_wb[FP_NORM_ROUND_WB_IDS.FMADD]), 
        .fp_mul_wb(intermediate_unit_wb[FP_NORM_ROUND_WB_IDS.FMUL])
    );

    fp_div_sqrt_wrapper div_sqrt_inst (
        .clk(clk),
        .rst(rst),
        .fp_div_sqrt_inputs(div_sqrt_inputs),
        .issue(intermediate_issue[FP_UNIT_IDS.FDIV_SQRT]), 
        .wb(intermediate_unit_wb[FP_NORM_ROUND_WB_IDS.FDIV_SQRT]) 
    );

    fp_wb2fp_misc wb2fp_misc_inst (
        .clk(clk),
        .issue(intermediate_issue[FP_UNIT_IDS.MISC_WB2FP]),
        .fp_wb2fp_misc_inputs(wb2fp_misc_inputs),
        .wb(intermediate_unit_wb[FP_NORM_ROUND_WB_IDS.MISC_WB2FP])
    );

    fp_wb2int_misc wb2int_misc_inst (
        .clk(clk),
        .issue(intermediate_issue[FP_UNIT_IDS.MISC_WB2INT]),
        .fp_wb2int_misc_inputs(wb2int_misc_inputs),
        .wb(int_wb)
    );

    ////////////////////////////////////////////////////
    //Normalization and rounding
    fp_normalize_rounding_top #(.NUM_WB_UNITS(FP_NUM_INTERMEDIATE_WB)) norm_round_inst (
        .clk(clk),
        .rst(rst),
        .intermediate_unit_wb(intermediate_unit_wb),
        .unit_wb(fp_wb)
    );

endmodule