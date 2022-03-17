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

module fp_sign_inj (
  input logic clk,
  input logic advance,
  unit_issue_interface.unit issue,
  input fp_sign_inject_inputs_t fp_sign_inject_inputs,
  fp_unit_writeback_interface.unit wb
);

  fp_sign_inject_inputs_t fp_sign_inject_inputs_r;
  logic [FLEN-1:0]        rs1;
  logic                   rs1_hidden_bit;
  logic                   rs2_sign;
  logic [2:0]             fn3;        
  logic [FLEN-1:0]        sign_inj_result;
  logic                   done;
  id_t                    id;

  ////////////////////////////////////////////////////
  //Implementation
  //Input Processing
  always_ff @ (posedge clk) begin
    if (advance) begin
      done <= issue.new_request;
      id <= issue.id;
      fp_sign_inject_inputs_r <= fp_sign_inject_inputs;
    end
  end

  assign rs1 = fp_sign_inject_inputs_r.rs1;
  assign rs1_hidden_bit = fp_sign_inject_inputs_r.rs1_hidden_bit;
  assign rs2_sign = fp_sign_inject_inputs_r.rs2_sign;
  assign fn3 = fp_sign_inject_inputs_r.rm;

  always_comb begin 
    case(fn3)
      default: sign_inj_result = {rs2_sign, rs1[FLEN-2:0]};
      3'b001:  sign_inj_result = {~rs2_sign, rs1[FLEN-2:0]};
      3'b010:  sign_inj_result = {rs2_sign ^ rs1[FLEN-1], rs1[FLEN-2:0]};
    endcase 
  end

  ////////////////////////////////////////////////////
  //Output
  assign wb.rd = sign_inj_result;
  assign wb.hidden = rs1_hidden_bit;
  assign wb.done = done;
  assign wb.id = id;
endmodule
