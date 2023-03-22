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

module fp_decode_and_issue
    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    import fpu_types::*;
    import fpu_types::*;
#(
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG,
        parameter FP_NUM_UNITS = 4,
        parameter fp_unit_id_param_t FP_UNIT_IDS = FP_EXAMPLE_UNIT_IDS
)(
    input logic clk,
    input logic rst,

    input decode_packet_t decode,
    fp_renamer_interface.decode fp_renamer,
    output logic fp_decode_uses_rd,
    output phys_addr_t fp_decode_phys_rd_addr,
    output phys_addr_t fp_decode_phys_rs_addr [FP_REGFILE_READ_PORTS],
    //output logic [$clog2(CONFIG.FP.FP_NUM_WB_GROUPS)-1:0] fp_decode_rs_wb_group [FP_REGFILE_READ_PORTS],
    output logic fp_decode_rs_wb_group [FP_REGFILE_READ_PORTS],
    output logic [FP_NUM_UNITS-1:0] unit_needed,

    output issue_packet_t issue,
    input logic issue_stage_ready,
    input logic instruction_issued,
    output logic fp_instruction_issued_with_rd,
    input logic [31:0] int_rs1_data,
    fp_register_file_issue_interface.issue fp_rf,
    output logic fp_operands_ready,
    input logic [2:0] dyn_rm,
    output fp_pre_processing_packet_t fp_pre_processing_packet,

    output id_t fp_store_forward_id,
    input logic gc_fetch_flush
);

    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Instruction aliases
    logic [4:0] rs1_addr;
    logic [4:0] rs2_addr;
    logic [4:0] rs3_addr;
    logic [4:0] rd_addr;
    logic [6:0] opcode;
    logic [6:0] fn7;
    logic [4:0] opcode_trim;

    logic is_single;
    logic is_i2f;
    logic is_f2i;
    logic is_class;
    logic is_fcmp;
    logic is_fld;
    logic is_sqrt;
    logic is_sign_inj, is_sign_inj_r;
    logic is_minmax, is_minmax_r;
    logic is_mv_f2i, is_mv_i2f;
    logic is_s2d, is_d2s;
    logic enable_pre_normalize;

    logic uses_rs1, uses_rs1_r;
    logic uses_rs2, uses_rs2_r;
    logic uses_rs3, uses_rs3_r;
    logic uses_rd;

    assign opcode = decode.instruction[6:0];
    assign opcode_trim = opcode[6:2];
    assign fn7 = decode.instruction[31:25];
    assign rs1_addr = decode.instruction[19:15];
    assign rs2_addr = decode.instruction[24:20];
    assign rs3_addr = decode.instruction[31:27];
    assign rd_addr = decode.instruction[11:7];

    assign is_single = ((opcode_trim inside {FMADD_T, FMSUB_T, FNMSUB_T, FNMADD_T, FOP_T} & ~fn7[0]) | (opcode_trim inside {FLD_T, FSD_T} & ~decode.instruction[12]) | is_s2d) & ~is_d2s;
    assign is_fld = opcode_trim == FLD_T;
    assign is_i2f = opcode_trim == FOP_T & fn7 inside {FCVT_DW, FCVT_SW};
    assign is_mv_i2f = opcode_trim == FOP_T & fn7 == FMV_WX;
    assign is_f2i = opcode_trim == FOP_T & fn7 inside {FCVT_WD, FCVT_WS};
    assign is_mv_f2i = opcode_trim == FOP_T & fn7 == FMV_XW;
    assign is_s2d = opcode_trim == FOP_T & fn7 == FCVT_DS;
    assign is_d2s = opcode_trim == FOP_T & fn7 == FCVT_SD;
    assign is_class = opcode_trim == FOP_T & (fn7 == FCLASS | (fn7 == FMV_XW & decode.instruction[12])); //FCLASS_F has the same fn7 as FMV_XW
    assign is_sqrt = opcode_trim == FOP_T & fn7 inside {FSQRT, FSQRT_F};
    assign is_fcmp = opcode_trim == FOP_T & fn7 inside {FCMP, FCMP_F};
    assign is_minmax = opcode_trim == FOP_T & fn7 inside {FMIN_MAX, FMIN_MAX_F};
    assign is_sign_inj = opcode_trim == FOP_T & fn7 inside {FSIGN_INJECTION, FSIGN_INJECTION_F};
    assign enable_pre_normalize = opcode_trim inside {FMADD_T, FMSUB_T, FNMSUB_T, FNMADD_T} | (opcode_trim == FOP_T & fn7 inside {FMUL, FDIV, FSQRT, FCVT_WD, FMUL_F, FDIV_F, FSQRT_F, FCVT_WS});//TODO: why are the converts here?

    ////////////////////////////////////////////////////
    //Register File Support
    assign uses_rs1 = opcode_trim inside {FMADD_T, FMSUB_T, FNMSUB_T, FNMADD_T} | (opcode_trim == FOP_T & fn7 inside {FADD, FSUB, FMUL, FDIV, FSQRT, FSIGN_INJECTION, FMIN_MAX, FCMP, FCVT_SD, FCLASS, FCVT_WD, FADD_F, FSUB_F, FMUL_F, FDIV_F, FSQRT_F, FSIGN_INJECTION_F, FMIN_MAX_F, FCMP_F, FCVT_DS, /*FCLASS_F,*/ FCVT_WS, FMV_XW});
    assign uses_rs2 = opcode_trim inside {FMADD_T, FMSUB_T, FNMSUB_T, FNMADD_T} | (opcode_trim == FOP_T & fn7 inside {FADD, FSUB, FMUL, FDIV, FSIGN_INJECTION, FMIN_MAX, FCMP, FADD_F, FSUB_F, FMUL_F, FDIV_F, FSIGN_INJECTION_F, FMIN_MAX_F, FCMP_F});
    assign uses_rs3 = opcode_trim inside {FMADD_T, FMSUB_T, FNMSUB_T, FNMADD_T};
    assign uses_rd = decode.wb2_float;

    ////////////////////////////////////////////////////
    //Unit Determination
    assign unit_needed[FP_UNIT_IDS.FMADD] = opcode[6-:3] == 3'b100 | (opcode_trim == FOP_T & fn7 inside{FMUL, FADD, FSUB, FMUL_F, FADD_F, FSUB_F});
    assign unit_needed[FP_UNIT_IDS.FDIV_SQRT] = opcode_trim inside {FOP_T} & (fn7[3:0] == 4'b1101 || fn7[3:0] == 4'b1100);
    assign unit_needed[FP_UNIT_IDS.MISC_WB2FP] = is_i2f | is_mv_i2f | is_minmax | is_sign_inj | is_s2d | is_d2s;
    assign unit_needed[FP_UNIT_IDS.MISC_WB2INT] = is_f2i | is_mv_f2i | is_fcmp | is_class;

    ////////////////////////////////////////////////////
    //Renamer Support
    assign fp_renamer.rd_addr = rd_addr;
    assign fp_renamer.rs_addr[RS1] = rs1_addr;
    assign fp_renamer.rs_addr[RS2] = rs2_addr;
    assign fp_renamer.rs_addr[RS3] = rs3_addr;
    assign fp_renamer.uses_rd = uses_rd;
    assign fp_renamer.rd_wb_group = 0; //FPU has only 1 wb_group ATM
    assign fp_renamer.id = decode.id;

    ////////////////////////////////////////////////////
    //Decode ID Support
    assign fp_decode_uses_rd = uses_rd;
    assign fp_decode_phys_rd_addr = fp_renamer.phys_rd_addr;
    assign fp_decode_phys_rs_addr[RS1] = fp_renamer.phys_rs_addr[RS1];
    assign fp_decode_phys_rs_addr[RS2] = fp_renamer.phys_rs_addr[RS2];
    assign fp_decode_phys_rs_addr[RS3] = fp_renamer.phys_rs_addr[RS3];
    assign fp_decode_rs_wb_group[RS1] = fp_renamer.rs_wb_group[RS1];
    assign fp_decode_rs_wb_group[RS2] = fp_renamer.rs_wb_group[RS2];
    assign fp_decode_rs_wb_group[RS3] = fp_renamer.rs_wb_group[RS3];

    ////////////////////////////////////////////////////
    //Issue
    //logic [FP_REGFILE_READ_PORTS-1:0][$clog2(CONFIG.FP.FP_NUM_WB_GROUPS)-1:0] fp_issue_rs_wb_group;
    logic [FP_REGFILE_READ_PORTS-1:0] fp_issue_rs_wb_group;

    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            issue.rs_addr[RS3] <= rs3_addr;
            uses_rs1_r <= uses_rs1;
            uses_rs2_r <= uses_rs2;
            uses_rs3_r <= uses_rs3;
            issue.fp_uses_rd <= uses_rd;
            issue.fp_phys_rs_addr[RS1] <= fp_renamer.phys_rs_addr[RS1];
            issue.fp_phys_rs_addr[RS2] <= fp_renamer.phys_rs_addr[RS2];
            issue.fp_phys_rs_addr[RS3] <= fp_renamer.phys_rs_addr[RS3];
            issue.fp_phys_rd_addr <= fp_renamer.phys_rd_addr;
            fp_issue_rs_wb_group <= fp_renamer.rs_wb_group;
            issue.is_float <= decode.is_float;
            issue.is_single <= is_single;
            issue.wb2_float <= decode.wb2_float;
            issue.accumulating_csrs <= decode.accumulating_csrs;
            issue.enable_pre_normalize <= enable_pre_normalize;
            issue.is_fld <= is_fld;
            issue.is_f2i <= is_f2i;
            issue.is_mv_f2i <= is_mv_f2i;
            issue.is_i2f <= is_i2f;
            issue.is_mv_i2f <= is_mv_i2f;
            issue.is_s2d <= is_s2d;
            issue.is_d2s <= is_d2s;
            issue.is_class <= is_class;
            issue.is_sign_inj <= is_sign_inj;
            issue.is_minmax <= is_minmax;
            issue.is_fcmp <= is_fcmp;
        end
    end

    ////////////////////////////////////////////////////
    //Issue Determination
    logic rs1_conflict, rs2_conflict, rs3_conflict;

    assign rs1_conflict = fp_rf.inuse[RS1] & uses_rs1_r;
    assign rs2_conflict = fp_rf.inuse[RS2] & uses_rs2_r;
    assign rs3_conflict = fp_rf.inuse[RS3] & uses_rs3_r;
    assign fp_operands_ready = (~rs1_conflict) & (~rs2_conflict) & (~rs3_conflict);

    assign fp_rf.phys_rs_addr[RS1] = issue.fp_phys_rs_addr[RS1];
    assign fp_rf.phys_rs_addr[RS2] = issue.fp_phys_rs_addr[RS2];
    assign fp_rf.phys_rs_addr[RS3] = issue.fp_phys_rs_addr[RS3];
    assign fp_rf.phys_rd_addr = issue.fp_phys_rd_addr;
    assign fp_rf.rs_wb_group[RS1] = fp_issue_rs_wb_group[RS1];
    assign fp_rf.rs_wb_group[RS2] = fp_issue_rs_wb_group[RS2];
    assign fp_rf.rs_wb_group[RS3] = fp_issue_rs_wb_group[RS3];

    assign fp_rf.single_cycle_or_flush = (issue.stage_valid & issue.fp_uses_rd & gc_fetch_flush);

    assign fp_instruction_issued_with_rd = instruction_issued & issue.wb2_float;

    ////////////////////////////////////////////////////
    //DYN Rounding mode support
    logic [2:0] rm;
    assign rm = &issue.fn3 ? dyn_rm : issue.fn3; //TODO: Although issue is an output, fn3 is treated as an input

    //FP store forwarding
    (* ramstyle = "MLAB, no_rw_check" *) id_t rd_to_id_table [32]; //separate table for fp id tracking to avoid overwriting
    always_ff @ (posedge clk) begin
        if (fp_instruction_issued_with_rd & issue.wb2_float)
            rd_to_id_table[issue.rd_addr] <= issue.id;
    end
    assign fp_store_forward_id = rd_to_id_table[issue.rs_addr[RS2]];

    ////////////////////////////////////////////////////
    //Pre processing packet
    assign fp_pre_processing_packet.rm = rm;
    assign fp_pre_processing_packet.issue = issue;
    assign fp_pre_processing_packet.rs1 = fp_rf.data[RS1];
    assign fp_pre_processing_packet.rs2 = fp_rf.data[RS2];
    assign fp_pre_processing_packet.rs3 = fp_rf.data[RS3];
    assign fp_pre_processing_packet.int_rs1 = int_rs1_data;
endmodule
