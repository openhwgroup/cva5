/*
 * Copyright © 2017-2019 Yuhui Gao, Eric Matthews, Lesley Shannon
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
    )
    (
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
        output logic is_i2f,
        output logic is_f2i,
        output logic is_class,
        output logic is_fcmp,

        output issue_packet_t issue,
        input logic issue_stage_ready,
        input logic instruction_issued,
        output logic fp_instruction_issued_with_rd,
        input logic [31:0] int_rs1_data,
        fp_register_file_issue_interface.issue fp_rf,
        output logic fp_operands_ready,
        input logic [2:0] dyn_rm,

        output id_t fp_store_forward_id,
        output fp_madd_inputs_t fp_madd_inputs,
        output fp_cmp_inputs_t fp_cmp_inputs,
        output fp_div_sqrt_inputs_t fp_div_sqrt_inputs,
        output fp_cvt_mv_inputs_t fp_cvt_mv_inputs,
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

    logic is_sqrt;

    logic uses_rs1;
    logic uses_rs2;
    logic uses_rs3;
    logic uses_rd;

    assign opcode = decode.instruction[6:0];
    assign opcode_trim = opcode[6:2];
    assign fn7 = decode.instruction[31:25];
    assign rs1_addr = decode.instruction[19:15];
    assign rs2_addr = decode.instruction[24:20];
    assign rs3_addr = decode.instruction[31:27];
    assign rd_addr = decode.instruction[11:7];

    assign is_i2f = opcode_trim == FOP_T & fn7 == FCVT_DW;
    assign is_f2i = opcode_trim == FOP_T & fn7 == FCVT_WD;
    assign is_class = opcode_trim == FOP_T & fn7 == FCLASS;
    assign is_sqrt = opcode_trim == FOP_T & fn7 == FSQRT;
    assign is_fcmp = opcode_trim == FOP_T & fn7 == FCMP;

    ////////////////////////////////////////////////////
    //Register File Support
    assign uses_rs1 = opcode_trim inside {FMADD_T, FMSUB_T, FNMSUB_T, FNMADD_T} | (opcode_trim == FOP_T & fn7 inside {FADD, FSUB, FMUL, FDIV, FSQRT, FSIGN_INJECTION, FMIN_MAX, FCMP, FCVT_SD, FCLASS, FCVT_WD});
    assign uses_rs2 = opcode_trim inside {FLD_T, FMADD_T, FMSUB_T, FNMSUB_T, FNMADD_T} | (opcode_trim == FOP_T & fn7 inside {FADD, FSUB, FMUL, FDIV, FSIGN_INJECTION, FMIN_MAX, FCMP});
    assign uses_rs3 = opcode_trim inside {FMADD_T, FMSUB_T, FNMSUB_T, FNMADD_T};
    assign uses_rd = decode.wb2_float;

    ////////////////////////////////////////////////////
    //Unit Determination
    assign unit_needed[FP_UNIT_IDS.FMADD] = opcode[6-:3] == 3'b100 | (opcode_trim == FOP_T & fn7 inside{FMUL, FADD, FSUB});
    assign unit_needed[FP_UNIT_IDS.FDIV_SQRT] = opcode_trim inside {FOP_T} & fn7[3:0] == 4'b1101;
    assign unit_needed[FP_UNIT_IDS.FMINMAX_CMP] = opcode_trim inside {FOP_T} & fn7 inside {FMIN_MAX, FCMP, FSIGN_INJECTION, FCLASS};
    assign unit_needed[FP_UNIT_IDS.FCVT] = opcode_trim inside {FOP_T} & fn7 inside {FCVT_SD, FCVT_DS, FCVT_DW, FCVT_WD};

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
    rs_addr_t fp_decode_rd_addr;

    assign fp_decode_uses_rd = uses_rd;
    assign fp_decode_rd_addr = rd_addr;
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
            issue.fn7 <= fn7;
            issue.fp_uses_rs1 <= uses_rs1;
            issue.fp_uses_rs2 <= uses_rs2;
            issue.fp_uses_rs3 <= uses_rs3;
            issue.fp_uses_rd <= uses_rd;
            issue.fp_phys_rs_addr[RS1] <= fp_renamer.phys_rs_addr[RS1];
            issue.fp_phys_rs_addr[RS2] <= fp_renamer.phys_rs_addr[RS2];
            issue.fp_phys_rs_addr[RS3] <= fp_renamer.phys_rs_addr[RS3];
            issue.fp_phys_rd_addr <= fp_renamer.phys_rd_addr;
            fp_issue_rs_wb_group <= fp_renamer.rs_wb_group;
            issue.is_float <= decode.is_float;
            issue.wb2_float <= decode.wb2_float;
            issue.accumulating_csrs <= decode.accumulating_csrs;
        end
    end

    ////////////////////////////////////////////////////
    //Issue Determination
    logic rs1_conflict, rs2_conflict, rs3_conflict;

    assign rs1_conflict = fp_rf.inuse[RS1] & issue.fp_uses_rs1;
    assign rs2_conflict = fp_rf.inuse[RS2] & issue.fp_uses_rs2;
    assign rs3_conflict = fp_rf.inuse[RS3] & issue.fp_uses_rs3;
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
    assign rm = &issue.fn3 ? dyn_rm : issue.fn3;

    ////////////////////////////////////////////////////
    //Special Case Detection
    localparam VARIABLE_EXPO_WIDTH = EXPO_WIDTH;
    localparam VARIABLE_FRAC_WIDTH = FRAC_WIDTH;
    logic is_inf[FP_REGFILE_READ_PORTS];
    logic is_SNaN[FP_REGFILE_READ_PORTS];
    logic is_QNaN[FP_REGFILE_READ_PORTS];
    logic is_zero[FP_REGFILE_READ_PORTS];
    logic hidden_bit[FP_REGFILE_READ_PORTS];

    fp_special_case_detection_sandboxed #(.SANDBOX_FRAC_W(VARIABLE_FRAC_WIDTH), .SANDBOX_EXPO_W(VARIABLE_EXPO_WIDTH))
      rs1_special_case_detection (
        .data_in (fp_rf.data[RS1]),
        .is_inf (is_inf[RS1]),
        .is_SNaN (is_SNaN[RS1]),
        .is_QNaN (is_QNaN[RS1]),
        .is_zero (is_zero[RS1]),
        .hidden (hidden_bit[RS1])
      );  

    fp_special_case_detection_sandboxed #(.SANDBOX_FRAC_W(VARIABLE_FRAC_WIDTH), .SANDBOX_EXPO_W(VARIABLE_EXPO_WIDTH))
      rs2_special_case_detection (
        .data_in (fp_rf.data[RS2]),
        .is_inf (is_inf[RS2]),
        .is_SNaN (is_SNaN[RS2]),
        .is_QNaN (is_QNaN[RS2]),
        .is_zero (is_zero[RS2]),
        .hidden (hidden_bit[RS2])
      );  

    fp_special_case_detection_sandboxed #(.SANDBOX_FRAC_W(VARIABLE_FRAC_WIDTH), .SANDBOX_EXPO_W(VARIABLE_EXPO_WIDTH))
      rs3_special_case_detection (
        .data_in (fp_rf.data[RS3]),
        .is_inf (is_inf[RS3]),
        .is_SNaN (is_SNaN[RS3]),
        .is_QNaN (is_QNaN[RS3]),
        .is_zero (is_zero[RS3]),
        .hidden (hidden_bit[RS3])
      );

    //FP store forwarding
    (* ramstyle = "MLAB, no_rw_check" *) id_t rd_to_id_table [32]; //separate table for fp id tracking to avoid overwriting
    always_ff @ (posedge clk) begin
        if (fp_instruction_issued_with_rd & issue.wb2_float)
            rd_to_id_table[issue.rd_addr] <= issue.id;
    end
    assign fp_store_forward_id = rd_to_id_table[issue.rs_addr[RS2]];

    //FMADD inputs
    logic is_fma, is_fadd, is_fmul;
    assign is_fma = issue.opcode[6:4] == 3'b100; //Fused multiply and add instruction
    assign is_fmul = issue.opcode[6:4] == 3'b101 & issue.fn7[3];
    assign is_fadd = issue.opcode[6:4] == 3'b101 & ~issue.fn7[3];
    assign fp_madd_inputs.instruction = {is_fma, is_fadd, is_fmul};
    assign fp_madd_inputs.rs1 = fp_rf.data[RS1];
    assign fp_madd_inputs.rs2 = fp_rf.data[RS2];
    assign fp_madd_inputs.rs3 = fp_rf.data[RS3];
    assign fp_madd_inputs.rs1_hidden_bit = hidden_bit[RS1];
    assign fp_madd_inputs.rs2_hidden_bit = hidden_bit[RS2];
    assign fp_madd_inputs.rs3_hidden_bit = hidden_bit[RS3];
    assign fp_madd_inputs.op = issue.opcode;
    assign fp_madd_inputs.rm = rm;
    assign fp_madd_inputs.fn7 = issue.fn7;
    assign fp_madd_inputs.rs1_special_case = {is_inf[RS1], is_SNaN[RS1], is_QNaN[RS1], is_zero[RS1]}; 
    assign fp_madd_inputs.rs2_special_case = {is_inf[RS2], is_SNaN[RS2], is_QNaN[RS2], is_zero[RS2]};
    assign fp_madd_inputs.rs3_special_case = {is_inf[RS3], is_SNaN[RS3], is_QNaN[RS3], is_zero[RS3]};

    ////////////////////////////////////////////////////
    //cmp/minmax
    assign fp_cmp_inputs.rs1 = fp_rf.data[RS1];
    assign fp_cmp_inputs.rs2 = fp_rf.data[RS2];
    assign fp_cmp_inputs.rs1_hidden_bit = hidden_bit[RS1];
    assign fp_cmp_inputs.rs2_hidden_bit = hidden_bit[RS2];
    assign fp_cmp_inputs.rm = rm;  
    assign fp_cmp_inputs.fn7 = issue.fn7;      
    assign fp_cmp_inputs.is_sign_inj = issue.fn7 == FSIGN_INJECTION;
    assign fp_cmp_inputs.is_class = issue.fn7 == FCLASS;
    assign fp_cmp_inputs.rs1_special_case = {is_inf[RS1], is_SNaN[RS1], is_QNaN[RS1], is_zero[RS1]};
    assign fp_cmp_inputs.rs2_special_case = {is_inf[RS2], is_SNaN[RS2], is_QNaN[RS2], is_zero[RS2]};

    ////////////////////////////////////////////////////
    //transfer  
    assign fp_cvt_mv_inputs.f2i_rs1 = fp_rf.data[RS1];
    assign fp_cvt_mv_inputs.f2i_rs1_hidden = hidden_bit[RS1];
    assign fp_cvt_mv_inputs.f2i_rs1_special_case = {is_inf[RS1], is_SNaN[RS1], is_QNaN[RS1], is_zero[RS1]};
    assign fp_cvt_mv_inputs.i2f_rs1 = int_rs1_data;
    assign fp_cvt_mv_inputs.rm = rm;
    //FMV.X.W/FMV.W.X
    //Only for rv32f
    assign fp_cvt_mv_inputs.is_mv = &issue.fn7[6:4]; // moves IEEE format in/out of f registers (only moing bit patterns)
    //FCVT.D.W(U)/FCVT.W(U).D
    assign fp_cvt_mv_inputs.is_float = ~issue.fn7[3]; //issue.fn7 inside {FCVT_WD, FMV_WX};
    assign fp_cvt_mv_inputs.is_signed = ~issue.rs_addr[RS2][0]; //rs2_addr determines if conversion is signed
    //FCVT.S.D/FCVT.D.S
    assign fp_cvt_mv_inputs.is_f2f = ~issue.fn7[6]; //issue.fn7 inside {FCVT_SD, FCVT_DS}; 
    assign fp_cvt_mv_inputs.is_d2s = issue.rs_addr[RS2][0];

    ////////////////////////////////////////////////////
    //div_sqrt
    assign fp_div_sqrt_inputs.rs1 = fp_rf.data[RS1];
    assign fp_div_sqrt_inputs.rs2 = fp_rf.data[RS2];
    assign fp_div_sqrt_inputs.rs1_hidden_bit = hidden_bit[RS1];
    assign fp_div_sqrt_inputs.rs2_hidden_bit = hidden_bit[RS2];
    assign fp_div_sqrt_inputs.rm = rm;
    assign fp_div_sqrt_inputs.fn7 = issue.fn7;
    assign fp_div_sqrt_inputs.id = issue.id;//fp_unit_issue[FP_DIV_SQRT_WB_ID].instruction_id;
    assign fp_div_sqrt_inputs.rs1_special_case = {is_inf[RS1], is_SNaN[RS1], is_QNaN[RS1], is_zero[RS1]}; 
    assign fp_div_sqrt_inputs.rs2_special_case = {is_inf[RS2], is_SNaN[RS2], is_QNaN[RS2], is_zero[RS2]};

endmodule
