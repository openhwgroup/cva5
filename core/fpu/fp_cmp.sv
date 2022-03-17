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

module fp_cmp (
    input logic clk,
    input logic advance,
    unit_issue_interface.unit issue,
    input fp_cmp_inputs_t fp_cmp_inputs,
    output flt_minmax, //output to minmax 
    unit_writeback_interface.unit wb
);

    logic [FLEN-1:0]        rs1;
    logic [FLEN-1:0]        rs2;
    logic [2:0]             fn3;        
    logic [6:0]             fn7;

    logic                   rs1_sign;
    logic [EXPO_WIDTH-1:0]  rs1_expo;
    logic [FRAC_WIDTH-1:0]  rs1_frac;
    logic                   rs1_NaN;
    logic                   rs1_SNaN;
    logic                   rs1_zero;
    logic                   rs2_sign;
    logic [EXPO_WIDTH-1:0]  rs2_expo;
    logic [FRAC_WIDTH-1:0]  rs2_frac;
    logic                   rs2_NaN;
    logic                   rs2_SNaN;
    logic                   rs2_zero;
    logic [3:0]             rs1_special_case;
    logic [3:0]             rs2_special_case;
    logic                   invalid_cmp, invalid_cmp_r;
    logic                   unordered, unordered_r;
    logic                   flt_intermediate;
    logic                   flt, feq, fle;
    logic [XLEN-1:0]        result, result_r;
    logic                   done, done_r;
    id_t                    id, id_r;

    ////////////////////////////////////////////////////
    //Implementation

    //Input processing
    assign rs1_sign = rs1[FLEN-1];
    assign rs1_expo = rs1[FLEN-2:FRAC_WIDTH];
    assign rs1_frac = rs1[FRAC_WIDTH-1:0];
    assign rs1_zero = rs1_special_case[0];
    assign rs1_NaN = |rs1_special_case[2:1];
    assign rs1_SNaN = |rs1_special_case[2];
    assign rs2_sign = rs2[FLEN-1];
    assign rs2_expo = rs2[FLEN-2:FRAC_WIDTH];
    assign rs2_frac = rs2[FRAC_WIDTH-1:0];
    assign rs2_NaN = |rs2_special_case[2:1];
    assign rs2_SNaN = |rs2_special_case[2];
    assign rs2_zero = rs2_special_case[0];

    assign invalid_cmp = ((fn3 != 3'b010) & (rs1_NaN | rs2_NaN)) |  // FLT FLE signaling comparison                  
                         ((fn3 == 3'b010) & (rs1_SNaN | rs2_SNaN)); // FEQ quiet comparison
    assign unordered = rs1_NaN | rs2_NaN;

    ////////////////////////////////////////////////////
    //FEQ
    assign feq = (rs1_zero && rs2_zero) || ((rs1_sign == rs2_sign) && (rs1_expo == rs2_expo) && (rs1_frac == rs2_frac));
    
    ////////////////////////////////////////////////////
    //FLT 
    always_comb begin 
      if (rs1_sign > rs2_sign) begin 
        //rs1 neg, rs2 pos
        flt_intermediate = 1;
      end else if (rs1_sign < rs2_sign) begin 
        //rs1 pos, rs2 neg
        flt_intermediate = 0;
      end else begin 
        //same sign
        case(rs1_sign)    //or rs2_sign, doesnt matter here
          0: begin 
            //both inputs are positive
            if (rs1_expo > rs2_expo) begin 
              flt_intermediate = 0;
            end else if (rs1_expo < rs2_expo) begin 
              flt_intermediate = 1;
            end else begin 
              //same exponent
              if (rs1_frac >= rs2_frac) begin 
                flt_intermediate = 0;
              end else begin 
                flt_intermediate = 1;
              end
            end
          end
          1: begin 
            //both inputs are negative
            if (rs1_expo > rs2_expo) begin 
              flt_intermediate = 1;
            end else if (rs1_expo < rs2_expo) begin 
              flt_intermediate = 0;
            end else begin 
              if (rs1_frac > rs2_frac) begin 
                flt_intermediate = 1;
              end else begin 
                flt_intermediate = 0;
              end
            end
          end
        endcase // rs1_sign
      end
      flt = flt_intermediate & ~(rs1_zero & rs2_zero); // +0 == -0
    end
    
    ////////////////////////////////////////////////////
    //FLE
    assign fle = flt || feq;

    ////////////////////////////////////////////////////
    //Register
    always_ff @ (posedge clk) begin
      if (advance) begin
        rs1 <= fp_cmp_inputs.rs1;
        rs2 <= fp_cmp_inputs.rs2;
        fn3 <= fp_cmp_inputs.rm;
        rs1_special_case <= fp_cmp_inputs.rs1_special_case;
        rs2_special_case <= fp_cmp_inputs.rs2_special_case;
        done <= issue.new_request;
        done_r <= done;
        id <= issue.id;
        id_r <= id;

        //cmp outputs are delayed by 1 cycles to match F2I's latency
        result_r <= result;
        invalid_cmp_r <= invalid_cmp;
        unordered_r <= unordered;
      end
    end

    ////////////////////////////////////////////////////
    //Output
    always_comb begin
      case(fn3)
        default: begin
          result = {{(XLEN-1){1'b0}},fle};
        end
        3'b001: begin
          result = {{(XLEN-1){1'b0}},flt};
        end
        3'b010: begin
          result = {{(XLEN-1){1'b0}},feq};
        end
      endcase 
    end

    assign wb.rd = result_r & {XLEN{~unordered_r}};
    assign wb.done = done_r;
    assign wb.id = id_r;
    assign wb.fflags = {invalid_cmp_r, 4'b0};

    //minmax outputs are delayed by 1 cycle 
    assign flt_minmax = flt_intermediate; // minmax distinguishes +-0, cmp does not

endmodule


