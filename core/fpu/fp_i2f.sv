/*
 * Copyright © 2017-2020 Yuhui Gao,  Lesley Shannon
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

import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module fp_i2f (
  input logic clk,
  unit_issue_interface.unit issue,
  input fp_i2f_inputs_t fp_i2f_inputs,
  fp_unit_writeback_interface.unit wb
);

  logic                            int_rs1_zero ;
  logic [XLEN-1:0]                 int_rs1_abs ;
  logic [EXPO_WIDTH-1:0]           i2f_int_width_minus_1;
  logic [4:0]                      clz ;
  fp_shift_amt_t                   i2f_clz, r_i2f_clz;
  logic                            int_rs1_sign;
  logic [EXPO_WIDTH-1:0]           i2f_expo;
  logic [FRAC_WIDTH-1:0]           i2f_frac;
  logic [2:0]                      i2f_grs;
  logic [FLEN-1:0]                 i2f_rd, r_i2f_rd;
  logic                            done, r_done;
  id_t                             id, r_id;

  ////////////////////////////////////////////////////
  //Implementation
  //The shifting is implemented using the post-normalization shifters
  //The integer is first placed to the right of the hidden bit, right-shifted
  //by 53 bits so that the integer bits are in the MSBs of the float. 
  //Then left shift the mantissa to normalize. The exponent should be initialized to 53

  assign int_rs1_abs = fp_i2f_inputs.int_rs1_abs;
  assign int_rs1_sign = fp_i2f_inputs.int_rs1_sign;
  assign int_rs1_zero = fp_i2f_inputs.int_rs1_zero;

  clz clz_inst(.clz_input(int_rs1_abs), .clz(clz));
  assign i2f_int_width_minus_1 = (XLEN - 1) - EXPO_WIDTH'(clz); 

  // handle reduced precision < XLEN
  generate if (FRAC_WIDTH >= XLEN) begin
    assign i2f_frac = {{(FRAC_WIDTH-XLEN){1'b0}}, int_rs1_abs};
    assign i2f_grs = 0; //the entire integer will fit in mantissa field
    assign i2f_clz = FRAC_WIDTH - i2f_int_width_minus_1;
  end else begin
    assign i2f_frac = int_rs1_abs[XLEN-1-:FRAC_WIDTH];
    assign i2f_grs = {int_rs1_abs[XLEN-1-FRAC_WIDTH-:2], |int_rs1_abs[XLEN-1-FRAC_WIDTH-2:0]};
    assign i2f_clz = $bits(fp_shift_amt_t)'(clz) + 1;
  end 
  endgenerate
  assign i2f_expo = (FRAC_WIDTH + BIAS) & {{EXPO_WIDTH{~int_rs1_zero}}};
  assign i2f_rd = {int_rs1_sign, i2f_expo, i2f_frac};

  ////////////////////////////////////////////////////
  //Registers
  //always_ff @ (posedge clk) begin
    //if (advance) begin
      //r_done <= done;
      //r_id <= id;
      //r_i2f_rd <= i2f_rd;
      //r_i2f_clz <= i2f_clz;
    //end
  //end

  ////////////////////////////////////////////////////
  //Output
  assign wb.rd = i2f_rd;
  assign wb.clz = i2f_clz;
  assign wb.done = issue.new_request;
  assign wb.id = issue.id;
endmodule

