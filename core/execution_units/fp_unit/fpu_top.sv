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

 module fpu_top

    import cva5_config::*;
    import cva5_types::*;
    import fpu_types::*;
    import opcodes::*;
    
    #(
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )
    (
        input logic clk,
        input logic rst,

        input decode_packet_t decode_stage,
        output logic unit_needed,
        output logic[REGFILE_READ_PORTS-1:0] uses_rs,
        output logic[2:0] fp_uses_rs,
        output logic uses_rd,
        output logic fp_uses_rd,

        input logic issue_stage_ready,
        input logic[2:0] dyn_rm,
        input logic[31:0] int_rf[REGFILE_READ_PORTS],
        input logic[FLEN-1:0] fp_rf[3],

        unit_issue_interface.unit issue,
        unit_writeback_interface.unit int_wb,
        unit_writeback_interface.unit fp_wb,
        output fflags_t fflags
    );

    fp_madd_inputs_t madd_inputs;
    fp_div_inputs_t div_inputs;
    fp_sqrt_inputs_t sqrt_inputs;
    fp_wb2fp_misc_inputs_t wb2fp_inputs;
    fp_wb2int_misc_inputs_t wb2int_inputs;
    fflags_t int_fflags;
    fflags_t fp_fflags;
    unit_issue_interface intermediate_issue[4:0](); //FMA, FDIV, FSQRT, WB2FP, WB2INT
    fp_intermediate_wb_interface intermediate_unit_wb[3:0](); //FMADD, FMUL, FDIV/FSQRT, WB2FP
    ////////////////////////////////////////////////////
    //Implementation
    //This unit instantiates the internal FPU components and connects them
    //It is also responsible for instruction decoding

    ////////////////////////////////////////////////////
    //Decode
    always_comb begin
        uses_rs = '0;
        uses_rs[RS1] = decode_stage.instruction inside {
            SP_FCVT_S_W, SP_FCVT_S_WU, SP_FMV_W_X,
            DP_FCVT_D_W, DP_FCVT_D_WU
        };

        fp_uses_rs = '0;
        fp_uses_rs[RS1] = decode_stage.instruction inside {
            SP_FMADD, SP_FMSUB, SP_FNMSUB, SP_FNMADD, SP_FADD, SP_FSUB, SP_FMUL,
            SP_FDIV, SP_FSQRT, SP_FSGNJ, SP_FSGNJN, SP_FSGNJX, SP_FMIN, SP_FMAX,
            SP_FCVT_W_S, SP_FCVT_WU_S, SP_FMV_X_W, SP_FEQ, SP_FLT, SP_FLE, SP_FCLASS,
            DP_FMADD, DP_FMSUB, DP_FNMSUB, DP_FNMADD, DP_FADD, DP_FSUB, DP_FMUL,
            DP_FDIV, DP_FSQRT, DP_FSGNJ, DP_FSGNJN, DP_FSGNJX, DP_FMIN, DP_FMAX,
            DP_FCVT_S_D, DP_FCVT_D_S, DP_FEQ, DP_FLT, DP_FLE, DP_FCLASS, DP_FCVT_W_D, DP_FCVT_WU_D
        };
        fp_uses_rs[RS2] = decode_stage.instruction inside {
            SP_FMADD, SP_FMSUB, SP_FNMSUB, SP_FNMADD, SP_FADD, SP_FSUB, SP_FMUL,
            SP_FDIV, SP_FSQRT, SP_FSGNJ, SP_FSGNJN, SP_FSGNJX, SP_FMIN, SP_FMAX,
            SP_FEQ, SP_FLT, SP_FLE,
            DP_FMADD, DP_FMSUB, DP_FNMSUB, DP_FNMADD, DP_FADD, DP_FSUB, DP_FMUL,
            DP_FDIV, DP_FSQRT, DP_FSGNJ, DP_FSGNJN, DP_FSGNJX, DP_FMIN, DP_FMAX,
            DP_FEQ, DP_FLT, DP_FLE
        };
        fp_uses_rs[RS3] = decode_stage.instruction inside {
            SP_FMADD, SP_FMSUB, SP_FNMSUB, SP_FNMADD,
            DP_FMADD, DP_FMSUB, DP_FNMSUB, DP_FNMADD
        };

        uses_rd = decode_stage.instruction inside {
            SP_FCVT_W_S, SP_FCVT_WU_S, SP_FMV_X_W, SP_FEQ, SP_FLT, SP_FLE, SP_FCLASS,
            DP_FEQ, DP_FLT, DP_FLE, DP_FCLASS, DP_FCVT_W_D, DP_FCVT_WU_D
        };
        fp_uses_rd = decode_stage.instruction inside {
            SP_FMADD, SP_FMSUB, SP_FNMSUB, SP_FNMADD, SP_FADD, SP_FSUB, SP_FMUL,
            SP_FDIV, SP_FSQRT, SP_FSGNJ, SP_FSGNJN, SP_FSGNJX, SP_FMIN, SP_FMAX,
            SP_FCVT_S_W, SP_FCVT_S_WU, SP_FMV_W_X,
            DP_FMADD, DP_FMSUB, DP_FNMSUB, DP_FNMADD, DP_FADD, DP_FSUB, DP_FMUL,
            DP_FDIV, DP_FSQRT, DP_FSGNJ, DP_FSGNJN, DP_FSGNJX, DP_FMIN, DP_FMAX,
            DP_FCVT_S_D, DP_FCVT_D_S, DP_FCVT_D_W, DP_FCVT_D_WU
        };

        unit_needed = decode_stage.instruction inside {
            SP_FMADD, SP_FMSUB, SP_FNMSUB, SP_FNMADD, SP_FADD, SP_FSUB, SP_FMUL,
            DP_FMADD, DP_FMSUB, DP_FNMSUB, DP_FNMADD, DP_FADD, DP_FSUB, DP_FMUL,
            SP_FDIV, SP_FSQRT,
            DP_FDIV, DP_FSQRT,
            SP_FSGNJ, SP_FSGNJN, SP_FSGNJX, SP_FMIN, SP_FMAX, SP_FCVT_S_W, SP_FCVT_S_WU, SP_FMV_W_X,
            DP_FSGNJ, DP_FSGNJN, DP_FSGNJX, DP_FMIN, DP_FMAX, DP_FCVT_S_D, DP_FCVT_D_S, DP_FCVT_D_W, DP_FCVT_D_WU,
            SP_FCVT_W_S, SP_FCVT_WU_S, SP_FMV_X_W, SP_FEQ, SP_FLT, SP_FLE, SP_FCLASS,
            DP_FEQ, DP_FLT, DP_FLE, DP_FCLASS, DP_FCVT_W_D, DP_FCVT_WU_D
        };
    end

    ////////////////////////////////////////////////////
    //Shared preprocessing
    logic is_single;
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
    logic neg_mul;
    logic conv_signed;
    logic is_sign_inj_single;
    rm_t rm_r;

    fp_preprocessing_packet_t pkt;
    assign pkt.valid = issue.new_request;
    assign pkt.unit[0] = is_fma | is_fmul | is_fadd;
    assign pkt.unit[1] = is_div;
    assign pkt.unit[2] = is_sqrt;
    assign pkt.unit[3] = is_i2f | is_mv_i2f | is_minmax | is_sign_inj | is_s2d | is_d2s;
    assign pkt.unit[4] = is_f2i | is_mv_f2i | is_fcmp | is_class;
    assign pkt.rs1 = fp_rf[RS1];
    assign pkt.rs2 = fp_rf[RS2];
    assign pkt.rs3 = fp_rf[RS3];
    assign pkt.int_rs1 = int_rf[RS1];
    assign pkt.id = issue.id;
    assign pkt.is_single = is_single;
    assign pkt.is_fma = is_fma;
    assign pkt.is_fadd = is_fadd;
    assign pkt.is_i2f = is_i2f;
    assign pkt.is_d2s = is_d2s;
    assign pkt.is_minmax = is_minmax;
    assign pkt.is_sign_inj = is_sign_inj;
    assign pkt.is_sign_inj_single = is_sign_inj_single;
    assign pkt.is_f2i = is_f2i;
    assign pkt.is_mv_i2f = is_mv_i2f;
    assign pkt.is_fcmp = is_fcmp;
    assign pkt.is_class = is_class;
    assign pkt.add = add;
    assign pkt.neg_mul = neg_mul;
    assign pkt.conv_signed = conv_signed;
    assign pkt.rm = &rm_r ? dyn_rm : rm_r;

    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            //Only the instructions that convert their arguments from s->d
            is_single <= decode_stage.instruction inside {SP_FMADD, SP_FMSUB, SP_FNMSUB, SP_FNMADD, SP_FADD, SP_FSUB, SP_FMUL, SP_FDIV, SP_FSQRT, SP_FMIN, SP_FMAX, SP_FCVT_S_W, SP_FCVT_S_WU, DP_FCVT_D_S, SP_FCVT_W_S, SP_FCVT_WU_S, SP_FEQ, SP_FLT, SP_FLE, SP_FCLASS};
            //Partial decoding to distinguish instructions from each other
            is_fma <= ~decode_stage.instruction[4];
            is_fmul <= decode_stage.instruction[4] & decode_stage.instruction[31:27] inside {5'b0??10};
            is_fadd <= decode_stage.instruction[4] & decode_stage.instruction[31:27] inside {5'b0000?};
            is_div <= decode_stage.instruction[4] & decode_stage.instruction[31:27] inside {5'b00?11};
            is_sqrt <= decode_stage.instruction[4] & decode_stage.instruction[31:27] inside {5'b01?1?};
            is_i2f <= decode_stage.instruction[4] & decode_stage.instruction[31:27] inside {5'b1?01?};
            is_mv_f2i <= decode_stage.instruction[4] & decode_stage.instruction[31:27] inside {5'b1110?} & ~decode_stage.instruction[12];
            is_s2d <= decode_stage.instruction[4] & decode_stage.instruction[31:27] inside {5'b01?0?} & ~decode_stage.instruction[20];
            is_d2s <= decode_stage.instruction[4] & decode_stage.instruction[31:27] inside {5'b01?0?} & decode_stage.instruction[20];
            is_minmax <= decode_stage.instruction[4] & decode_stage.instruction[31:27] inside {5'b0?1?1};
            is_sign_inj <= decode_stage.instruction[4] & decode_stage.instruction[31:27] inside {5'b0?1?0};
            is_sign_inj_single <= ~decode_stage.instruction[25];
            is_f2i <= decode_stage.instruction[4] & decode_stage.instruction[31:27] inside {5'b1?00?};
            is_mv_i2f <= decode_stage.instruction[4] & decode_stage.instruction[31:27] inside {5'b1?11?};
            is_fcmp <= decode_stage.instruction[4] & decode_stage.instruction[31:27] inside {5'b10???};
            is_class <= decode_stage.instruction[4] & decode_stage.instruction[31:27] inside {5'b1110?} & decode_stage.instruction[12];
            //Double duty for both FADD and FMA
            add <= decode_stage.instruction[4] ? ~decode_stage.instruction[27] : decode_stage.instruction[3:2] inside {2'b00, 2'b10};
            neg_mul <= decode_stage.instruction[3];
            conv_signed <= ~decode_stage.instruction[20];
            rm_r <= decode_stage.instruction[14:12];
        end
    end

    fp_preprocessing #(.CONFIG(CONFIG), .FP_NUM_UNITS(5)) fp_preprocessing_inst (
        .unit_issue(intermediate_issue),
        .pkt(pkt),
        .ready(issue.ready),
        .madd_args(madd_inputs),
        .div_args(div_inputs),
        .sqrt_args(sqrt_inputs),
        .wb2fp_args(wb2fp_inputs),
        .wb2int_args(wb2int_inputs),
    .*);

    ////////////////////////////////////////////////////
    //Execution Units
    fp_madd_wrapper #(.CONFIG(CONFIG)) fp_madd_inst (
        .args(madd_inputs),
        .issue(intermediate_issue[0]),
        .madd_wb(intermediate_unit_wb[1]),
        .mul_wb(intermediate_unit_wb[2]),
    .*);

    fp_div_sqrt_wrapper div_sqrt_inst (
        .div_inputs(div_inputs),
        .sqrt_inputs(sqrt_inputs),
        .div_issue(intermediate_issue[1]),
        .sqrt_issue(intermediate_issue[2]),
        .wb(intermediate_unit_wb[0]),
    .*);

    fp_wb2fp_misc wb2fp_misc_inst (
        .args(wb2fp_inputs),
        .issue(intermediate_issue[3]),
        .wb(intermediate_unit_wb[3])
    );

    fp_wb2int_misc wb2int_misc_inst (
        .args(wb2int_inputs),
        .issue(intermediate_issue[4]),
        .wb(int_wb),
        .fflags(int_fflags),
    .*);

    ////////////////////////////////////////////////////
    //Normalization and rounding
    fp_normalize_rounding_top #(.NUM_WB_UNITS(4)) norm_round_inst (
        .intermediate_wb(intermediate_unit_wb),
        .wb(fp_wb),
        .fflags(fp_fflags),
    .*);

    ////////////////////////////////////////////////////
    //Updating flags
    //Combine both wb2int and wb2fp in one because they can writeback simultaneously
    logic fp_accepted;
    logic int_accepted;
    assign fp_accepted = fp_wb.done & fp_wb.ack;
    assign int_accepted = int_wb.done & int_wb.ack;

    always_comb begin
        fflags = '0;
        if (fp_accepted & int_accepted)
            fflags = fp_fflags | int_fflags;
        else if (fp_accepted)
            fflags = fp_fflags;
        else if (int_accepted)
            fflags = int_fflags;
    end

endmodule
