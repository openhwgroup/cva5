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

module fp_minmax (
    input logic clk,
    input logic advance,
    unit_issue_interface.unit issue,
    input fp_minmax_inputs_t fp_minmax_inputs,
    input logic flt_minmax, //input from fcmp
    fp_unit_writeback_interface.unit wb
);
  
    fp_minmax_inputs_t fp_minmax_inputs_r;
    logic [FLEN-1:0]        rs1;
    logic [FLEN-1:0]        rs2;
    logic [2:0]             fn3;        //mode selection
    logic                   rs1_hidden_bit;
    logic                   rs2_hidden_bit;
    logic [3:0]             rs1_special_case;
    logic [3:0]             rs2_special_case;
    logic                   rs1_SNaN;
    logic                   rs1_QNaN;
    logic                   rs1_inf;
    logic                   rs1_subnormal;
    logic                   rs1_zero;
    logic                   rs2_SNaN;
    logic                   rs2_QNaN;
    logic                   rs2_inf;
    logic                   rs2_subnormal;
    logic                   rs2_zero;
    logic                   invalid_minmax;
    logic                   flt;
    logic [FLEN-1:0]        min_result, max_result;
    logic                   min_hidden, max_hidden;
    logic                   done;
    id_t                    id;

    ////////////////////////////////////////////////////
    //Implementation
    //Input Processing
    
    assign fn3 = fp_minmax_inputs_r.rm;
    assign rs1 = fp_minmax_inputs_r.rs1;
    assign rs1_hidden_bit = fp_minmax_inputs_r.rs1_hidden_bit;
    assign rs1_special_case = fp_minmax_inputs_r.rs1_special_case;
    assign rs2 = fp_minmax_inputs_r.rs2;
    assign rs2_hidden_bit = fp_minmax_inputs_r.rs2_hidden_bit;
    assign rs2_special_case = fp_minmax_inputs_r.rs2_special_case;

    assign rs1_SNaN = rs1_special_case[2];
    assign rs1_QNaN = rs1_special_case[1];
    assign rs2_SNaN = rs2_special_case[2];
    assign rs2_QNaN = rs2_special_case[1];

    //Special Case
    assign invalid_minmax = rs1_SNaN | rs2_SNaN;

    //min max results 
    always_comb begin 
        case({rs1_SNaN | rs1_QNaN, rs2_SNaN | rs2_QNaN})
          2'b11: begin 
            //return quiet NaN if both inputs are NaNs
            min_result = CANONICAL_NAN;
            min_hidden = 1;
            max_result = CANONICAL_NAN;
            max_hidden = 1;
          end
          2'b10: begin 
            //rs1 == NaN
            min_result = rs2;
            max_result = rs2;
            min_hidden = rs1_hidden_bit;
            max_hidden = rs1_hidden_bit;
          end
          2'b01: begin 
            //rs2 == NaN
            min_result = rs1;
            max_result = rs1;
            min_hidden = rs1_hidden_bit;
            max_hidden = rs1_hidden_bit;
          end
          2'b00: begin
            //both inputs normal
            min_result = (flt_minmax == 1) ? rs1 : rs2;
            min_hidden = (flt_minmax == 1) ? rs1_hidden_bit : rs2_hidden_bit;
            max_result = (flt_minmax == 1) ? rs2 : rs1;
            max_hidden = (flt_minmax == 1) ? rs2_hidden_bit : rs1_hidden_bit;
          end
        endcase
    end

    ////////////////////////////////////////////////////
    //Registers
    always_ff @ (posedge clk) begin
      if (advance) begin
        done <= issue.new_request;
        id <= issue.id;
        fp_minmax_inputs_r <= fp_minmax_inputs;
      end
    end
   
    ////////////////////////////////////////////////////
    //Output
    assign wb.rd = (fn3[0] == 1) ? max_result : min_result;
    assign wb.hidden = (fn3[0] == 1) ? max_hidden : min_hidden;
    assign wb.fflags = {invalid_minmax, 4'b0};
    assign wb.done = done;
    assign wb.id = id;
endmodule 
