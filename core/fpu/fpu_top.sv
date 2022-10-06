/*
 * Copyright © 2017, 2018, 2019 Eric Matthews,  Lesley Shannon
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
 *                  Yuhui Gao <yuhuig@sfu.ca>
 */

import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module fpu_top #(
      parameter FP_NUM_UNITS,                       //issue interfaces
      parameter fp_unit_id_param_t FP_UNIT_IDS,     //issue interface IDs
      parameter FP_NUM_WB_UNITS,                    //fp wb interfaces
      parameter fp_wb_id_param_t FP_WB_IDS,         //fp wb interface IDs
      parameter FP_NUM_NORM_ROUND_UNITS,            
      parameter fp_wb_norm_round_param_t FP_NORM_ROUND_WB_IDS, //intermediate wb IDs
      parameter FP_WB_INT_NUM_UNITS = 1,            //int wb interfaces
      parameter fp_wb_int_id_param_t FP_WB_INT_IDS  //int wb interface IDs
    ) 
    (
      input logic clk,
      input logic rst,
      input fp_pre_processing_packet_t fp_pre_processing_packet,
      output logic issue_advance,
      unit_issue_interface.unit fp_unit_issue [FP_NUM_UNITS-1:0], 
      unit_writeback_interface.unit unit_wb [FP_WB_INT_NUM_UNITS],
      fp_unit_writeback_interface.unit fp_unit_wb [FP_NUM_WB_UNITS]
    );


  /////////////////////////////////////////////////
  //Pre-processing
  unit_issue_interface debug_fp_unit_issue [FP_NUM_UNITS-1:0] (); 
  fp_madd_inputs_t fp_madd_inputs_pre_processed;
  fp_div_sqrt_inputs_t fp_div_sqrt_inputs_pre_processed;
  fp_wb2fp_misc_inputs_t fp_wb2fp_misc_inputs_pre_processed;
  fp_wb2int_misc_inputs_t fp_wb2int_misc_inputs_pre_processed;

  fp_pre_processing #(
    .FP_NUM_UNITS(FP_NUM_UNITS),
    .FP_UNIT_IDS(FP_UNIT_IDS)
  ) fp_pre_processing_inst (
    .clk(clk),
    .rst(rst),
    .i_fp_unit_issue(fp_unit_issue),
    .issue_advance(issue_advance),
    .o_fp_unit_issue(debug_fp_unit_issue),
    .i_fp_pre_processing_packet(fp_pre_processing_packet),
    .o_fp_madd_inputs(fp_madd_inputs_pre_processed),
    .o_fp_div_sqrt_inputs(fp_div_sqrt_inputs_pre_processed),
    .o_fp_wb2fp_misc_inputs(fp_wb2fp_misc_inputs_pre_processed),
    .o_fp_wb2int_misc_inputs(fp_wb2int_misc_inputs_pre_processed)
  );

  /////////////////////////////////////////////////
  //Execution units
  fp_madd_fused_top fp_madd_inst (
    .clk (clk),
    .rst (rst),
    .fp_madd_inputs (fp_madd_inputs_pre_processed),
    .issue(debug_fp_unit_issue[FP_UNIT_IDS.FMADD]), 
    .fp_madd_wb(intermediate_unit_wb[FP_NORM_ROUND_WB_IDS.FMADD]), 
    .fp_mul_wb (intermediate_unit_wb[FP_NORM_ROUND_WB_IDS.FMUL])
  );

  fp_div_sqrt_wrapper div_sqrt_inst (
    .clk (clk),
    .rst (rst),
    .fp_div_sqrt_inputs (fp_div_sqrt_inputs_pre_processed),
    .issue(debug_fp_unit_issue[FP_UNIT_IDS.FDIV_SQRT]), 
    .wb(intermediate_unit_wb[FP_NORM_ROUND_WB_IDS.FDIV_SQRT]) 
  );

  fp_wb2fp_misc wb2fp_misc_inst(
    .clk (clk),
    .issue (debug_fp_unit_issue[FP_UNIT_IDS.MISC_WB2FP]),
    .fp_wb2fp_misc_inputs (fp_wb2fp_misc_inputs_pre_processed),
    .wb (intermediate_unit_wb[FP_NORM_ROUND_WB_IDS.MISC_WB2FP])
  );

  fp_wb2int_misc wb2int_misc_inst(
    .clk (clk),
    .issue (debug_fp_unit_issue[FP_UNIT_IDS.MISC_WB2INT]),
    .fp_wb2int_misc_inputs (fp_wb2int_misc_inputs_pre_processed),
    .wb (unit_wb[FP_WB_INT_IDS.MISC_WB2INT])
  );

  /////////////////////////////////////////////////
  //Normalization and rounding
  fp_unit_writeback_interface intermediate_unit_wb [FP_NUM_NORM_ROUND_UNITS](); //units that require normalization/rounding
  localparam int unsigned FP_NUM_NORM_ROUND_UNITS_PER_PORT [FP_NUM_WB_GROUPS] = '{FP_NUM_NORM_ROUND_UNITS};
  fp_normalize_rounding_top #(
    .NUM_WB_UNITS(FP_NUM_NORM_ROUND_UNITS),
    .NUM_UNITS(FP_NUM_NORM_ROUND_UNITS_PER_PORT)
  ) 
  norm_round_inst(
    .clk(clk),
    .rst(rst),
    .intermediate_unit_wb(intermediate_unit_wb),
    .unit_wb(fp_unit_wb[FP_WB_IDS.FP_ARITH])
  );

endmodule
