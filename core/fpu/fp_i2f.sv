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
  input logic advance,
  unit_issue_interface.unit issue,
  input fp_i2f_inputs_t fp_i2f_inputs,
  fp_unit_writeback_interface.unit wb
);

  fp_i2f_inputs_t                  fp_i2f_inputs_r;
  logic                            is_signed;
  logic [XLEN-1:0]                 rs1_int;
  logic [XLEN-1:0]                 neg_i2f_rs1;
  logic                            rs1_zero [1:0];
  logic [XLEN-1:0]                 rs1_int_abs [1:0];
  logic [EXPO_WIDTH-1:0]           i2f_int_width_minus_1;
  logic [4:0]                      clz [1:0];
  fp_shift_amt_t                   i2f_clz;
  logic                            i2f_sign[1:0];
  logic [EXPO_WIDTH-1:0]           i2f_expo;
  logic [FRAC_WIDTH-1:0]           i2f_frac;
  logic [2:0]                      i2f_grs;
  logic [FLEN-1:0]                 i2f_rd;
  logic                            done;
  id_t                             id;

  ////////////////////////////////////////////////////
  //Implementation
  assign is_signed = fp_i2f_inputs.is_signed;

  //Input Integer Abs()
  assign rs1_int = fp_i2f_inputs.i2f_rs1;
  assign neg_i2f_rs1 = -rs1_int;
  always_comb begin
    if (is_signed & rs1_int[XLEN-1]) begin
      //signed integer &&  MSB == 1
      i2f_sign[0] = 1'b1; 
      rs1_int_abs[0] = neg_i2f_rs1;
    end else begin 
      i2f_sign[0] = 1'b0; 
      rs1_int_abs[0] = rs1_int;          
    end
  end
  assign rs1_zero[0] = ~|rs1_int;

  // Find the number of valid bits (excluding leaeding 0s) in the integer minus 1
  clz clz_inst(.clz_input(rs1_int_abs[1]), .clz(clz[1]));
  assign i2f_int_width_minus_1 = (XLEN - 1) - EXPO_WIDTH'(clz[1]); 

  // handle reduced precision < XLEN
  generate if (FRAC_WIDTH >= XLEN) begin
    assign i2f_frac = {{(FRAC_WIDTH-XLEN){1'b0}}, rs1_int_abs[1]};
    assign i2f_grs = 0; //the entire integer will fit in mantissa field
    assign i2f_clz = FRAC_WIDTH - i2f_int_width_minus_1;
  end else begin
    assign i2f_frac = rs1_int_abs[1][XLEN-1-:FRAC_WIDTH];
    assign i2f_grs = {rs1_int_abs[1][XLEN-1-FRAC_WIDTH-:2], |rs1_int_abs[1][XLEN-1-FRAC_WIDTH-2:0]};
    assign i2f_clz = $bits(fp_shift_amt_t)'(clz[1]) + 1;
  end endgenerate
  assign i2f_expo = (FRAC_WIDTH + BIAS) & {{EXPO_WIDTH{~rs1_zero[1]}}};
  assign i2f_rd = {i2f_sign[1], i2f_expo, i2f_frac};

  ////////////////////////////////////////////////////
  //Registers
  always_ff @ (posedge clk) begin 
    if (advance) begin 
      done <= issue.new_request;
      id <= issue.id;
      fp_i2f_inputs_r <= fp_i2f_inputs;
      i2f_sign[1] <= i2f_sign[0];
      rs1_zero[1] <= rs1_zero[0];
      rs1_int_abs[1] <= rs1_int_abs[0];
      //clz[1] <= clz[0]; 
    end
  end

  ////////////////////////////////////////////////////
  //Output
  assign wb.rd = i2f_rd;
  assign wb.clz = i2f_clz;
  assign wb.grs = {i2f_grs, {($bits(grs_t)-3){1'b0}}};
  assign wb.fflags = 0;
  assign wb.hidden = 0;
  assign wb.rm = fp_i2f_inputs_r.rm;
  assign wb.done = done;
  assign wb.id = id;
endmodule

