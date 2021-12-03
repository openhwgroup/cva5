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
      parameter FP_WB_INT_NUM_UNITS = 2,            //int wb interfaces
      parameter fp_wb_int_id_param_t FP_WB_INT_IDS  //int wb interface IDs
    ) 
    (
      input logic clk,
      input logic rst,
      input fp_madd_inputs_t fp_madd_inputs,
      input fp_cmp_inputs_t fp_cmp_inputs,
      input fp_div_sqrt_inputs_t fp_div_sqrt_inputs,
      input fp_cvt_mv_inputs_t fp_cvt_mv_inputs,
      unit_issue_interface fp_unit_issue [FP_NUM_UNITS-1:0], 
      unit_writeback_interface unit_wb [FP_WB_INT_NUM_UNITS],
      fp_unit_writeback_interface fp_unit_wb [FP_NUM_WB_UNITS]
    );

  fp_madd_fused_top fp_madd_inst (
    .clk (clk),
    .rst (rst),
    .fp_madd_inputs (fp_madd_inputs),
    .issue(fp_unit_issue[FP_UNIT_IDS.FMADD]), 
    .fp_madd_wb(fp_unit_wb[FP_WB_IDS.FMADD]), 
    .fp_mul_wb (fp_unit_wb[FP_WB_IDS.FMUL])
  );

  fp_cmp fp_cmp_inst (
    .clk (clk),
    .rst (rst), 
    .fp_cmp_inputs (fp_cmp_inputs),
    .issue (fp_unit_issue[FP_UNIT_IDS.FMINMAX_CMP]), 
    .cmp_wb (unit_wb[FP_WB_INT_IDS.FCMP]), 
    .minmax_wb (fp_unit_wb[FP_WB_IDS.FMINMAX])
  );

  fp_cvt_top fp_cvt_mv_inst (
    .clk (clk),
    .rst (rst), 
    .fp_cvt_mv_inputs (fp_cvt_mv_inputs),
    .issue(fp_unit_issue[FP_UNIT_IDS.FCVT]), 
    .f2i_wb(unit_wb[FP_WB_INT_IDS.FCVT_F2I]), 
    .i2f_wb(fp_unit_wb[FP_WB_IDS.FCVT_I2F])
  );

  fp_div_sqrt_wrapper div_sqrt_inst (
    .clk (clk),
    .rst (rst),
    .fp_div_sqrt_inputs (fp_div_sqrt_inputs),
    .issue(fp_unit_issue[FP_UNIT_IDS.FDIV_SQRT]), 
    .wb(fp_unit_wb[FP_WB_IDS.FDIV_SQRT]) 
  );
endmodule





