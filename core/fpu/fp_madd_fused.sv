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
import taiga_types::*;
import l2_config_and_types::*;
import fpu_types::*;

module fp_madd_fused_top (
  input logic clk,
  input logic rst,
  input fp_madd_inputs_t fp_madd_inputs,
  unit_issue_interface.unit issue,
  fp_unit_writeback_interface.unit fp_madd_wb,
  fp_unit_writeback_interface.unit fp_mul_wb 
  );

  logic is_fma, is_fadd, is_fmul;
  assign {is_fma, is_fadd, is_fmul} = fp_madd_inputs.instruction;

  ////////////////////////////////////////////////////////
  //FP_MUL Unit
  unit_issue_interface mul_issue(); 
  fp_unit_writeback_t fmul_wb; //writeback for fmul instructions
  fma_mul_outputs_t fma_mul_outputs, fma_mul_outputs_r; //intermediate writeback for fmadd instructions
  //logic [4:0] fmul_fflags;

  assign mul_issue.new_request = (is_fma | is_fmul) & issue.new_request; 
  assign mul_issue.id = issue.id;
  fp_mul_madd_fused MUL (
    .clk(clk),
    .rst(rst),
    .fp_madd_inputs(fp_madd_inputs),
    .issue(mul_issue),
    .fp_wb(fp_mul_wb),
    //.fflags(fmul_fflags),
    .fma_mul_outputs(fma_mul_outputs)
  );

  always_ff @ (posedge clk) begin
    if (add_issue.ready)// & fma_mul_outputs.mul_wb.done) 
      fma_mul_outputs_r <= fma_mul_outputs;
  end

  ////////////////////////////////////////////////////////
  //Process Intermediate Outputs
  //Prepare FMADD Adder Inputs
  fp_unit_writeback_t     fma_mul_wb;
  logic                   mul_op;
  logic                   add_op;
  logic                   fma_mul_invalid_operation;
  logic [2:0]             fma_mul_instruction;
  grs_t                   fma_mul_grs;
  logic [FLEN-1:0]        fma_add_rs1;
  logic                   fma_add_rs1_sign;
  logic                   fma_mul_norm_active;
  logic                   add_invalid_operation;
  logic [EXPO_WIDTH:0]    expo_diff;
  logic [EXPO_WIDTH:0]    expo_diff_negate;
  logic [EXPO_WIDTH:0]    expo_diff_to_add;
  logic                   swap;
  grs_t                   fp_add_grs;

  assign fma_mul_wb = fma_mul_outputs_r.mul_wb;
  assign mul_op = fma_mul_outputs_r.mul_op;
  assign add_op = fma_mul_outputs_r.add_op;
  assign fma_mul_invalid_operation = fma_mul_outputs_r.invalid_operation;
  assign fma_mul_instruction = fma_mul_outputs_r.instruction;
  assign fma_mul_grs = fma_mul_outputs_r.mul_grs;//mul_op == 1 ? ~fma_mul_outputs_r.mul_grs : fma_mul_outputs_r.mul_grs;
  assign fma_add_rs1 = fma_mul_wb.rd;
  assign fma_add_rs1_sign = mul_op ^ fma_add_rs1[FLEN-1];
  assign fma_add_inputs.rs1 = {fma_add_rs1_sign, fma_add_rs1[FLEN-2:0]};
  assign fma_add_inputs.rs1_special_case = fma_mul_outputs_r.rs1_special_case;//4'(fma_mul_outputs_r.rs1_zero);
  assign fma_add_inputs.rs1_hidden_bit = fma_mul_outputs_r.mul_wb_rd_hidden;
  assign fma_add_inputs.rs1_safe_bit = fma_mul_outputs_r.mul_wb_rd_safe;
  assign fma_add_inputs.rs1_expo_overflow = fma_mul_outputs_r.mul_wb_rd_expo_overflow;
  assign fma_add_inputs.rs2 = fma_mul_outputs_r.rs3; 
  assign fma_add_inputs.rs2_special_case = fma_mul_outputs_r.rs2_special_case;
  assign fma_add_inputs.rs2_hidden_bit = fma_mul_outputs_r.rs3_hidden_bit;
  assign fma_add_inputs.rm = fma_mul_outputs_r.mul_rm;
  assign fma_add_inputs.fn7 = (add_op == 0) ? FADD : FSUB;
  assign fma_mul_norm_active = fma_mul_wb.done; 

  ////////////////////////////////////////////////////////
  //FADD instruction inputs FIFO
  fp_add_inputs_t         add_inputs_fifo_data_in; 

  typedef struct packed {
    fp_add_inputs_t fp_add_inputs;
    id_t id;
    logic [EXPO_WIDTH:0] expo_diff;
    logic swap;
  } add_input_struct_t;
  add_input_struct_t add_inputs, add_inputs_from_fifo; 

  fifo_interface #(.DATA_WIDTH($bits(add_input_struct_t))) fp_add_inputs_fifo();

  assign add_inputs_fifo_data_in.rs1 = fp_madd_inputs.rs1;
  assign add_inputs_fifo_data_in.rs1_special_case = fp_madd_inputs.rs1_special_case;
  assign add_inputs_fifo_data_in.rs1_hidden_bit = fp_madd_inputs.rs1_hidden_bit;
  assign add_inputs_fifo_data_in.rs1_safe_bit = 0;
  assign add_inputs_fifo_data_in.rs1_expo_overflow = 0;
  assign add_inputs_fifo_data_in.rs2 = fp_madd_inputs.rs2;
  assign add_inputs_fifo_data_in.rs2_special_case = fp_madd_inputs.rs2_special_case;
  assign add_inputs_fifo_data_in.rs2_hidden_bit = fp_madd_inputs.rs2_hidden_bit;
  assign add_inputs_fifo_data_in.rs2_safe_bit = 0;
  assign add_inputs_fifo_data_in.rm = fp_madd_inputs.rm;
  assign add_inputs_fifo_data_in.fn7 = fp_madd_inputs.fn7;
  assign add_inputs.fp_add_inputs = add_inputs_fifo_data_in;
  assign add_inputs.id = issue.id;
  //pre calculate expo diff for FADD
  generate if (ENABLE_SUBNORMAL) begin
    // subnormal expo is implicitly set to 1
    assign expo_diff = (fp_madd_inputs.rs1[FLEN-2-:EXPO_WIDTH] + {{(EXPO_WIDTH-1){1'b0}}, ~fp_madd_inputs.rs1_hidden_bit})-
                       (fp_madd_inputs.rs2[FLEN-2-:EXPO_WIDTH] + {{(EXPO_WIDTH-1){1'b0}}, ~fp_madd_inputs.rs2_hidden_bit});
    assign expo_diff_negate = (fp_madd_inputs.rs2[FLEN-2-:EXPO_WIDTH] + {{(EXPO_WIDTH-1){1'b0}}, ~fp_madd_inputs.rs2_hidden_bit}) -
                              (fp_madd_inputs.rs1[FLEN-2-:EXPO_WIDTH] + {{(EXPO_WIDTH-1){1'b0}}, ~fp_madd_inputs.rs1_hidden_bit});
  end else begin
    assign expo_diff = (fp_madd_inputs.rs1[FLEN-2-:EXPO_WIDTH]) - (fp_madd_inputs.rs2[FLEN-2-:EXPO_WIDTH]);
    assign expo_diff_negate = (fp_madd_inputs.rs2[FLEN-2-:EXPO_WIDTH]) - (fp_madd_inputs.rs1[FLEN-2-:EXPO_WIDTH]);
  end endgenerate
  assign add_inputs.expo_diff = expo_diff[EXPO_WIDTH] ? expo_diff_negate : expo_diff;
  assign add_inputs.swap = expo_diff[EXPO_WIDTH] ? 1 : |expo_diff[EXPO_WIDTH-1:0] ? 0 : fp_madd_inputs.rs1[0+:FRAC_WIDTH] < fp_madd_inputs.rs2[0+:FRAC_WIDTH];

  //reduce fifo depth; change add ready signal
  assign fp_add_inputs_fifo.data_in = add_inputs;
  assign fp_add_inputs_fifo.potential_push = is_fadd & issue.new_request;
  assign fp_add_inputs_fifo.push = fp_add_inputs_fifo.potential_push;
  //assign fp_add_inputs_fifo.supress_push = 0;
  assign fp_add_inputs_fifo.pop = ~fma_mul_instruction[2] & fp_add_inputs_fifo.valid & add_issue.ready;
  assign add_inputs_from_fifo = fp_add_inputs_fifo.data_out;
  taiga_fifo #(.DATA_WIDTH($bits(add_input_struct_t)), .FIFO_DEPTH(2)) add_input_fifo (.fifo(fp_add_inputs_fifo), .*); 

  ////////////////////////////////////////////////////////
  //Adder input select
  //Prioritize FMADD
  fp_add_inputs_t         fp_add_inputs; //add inputs issued to adder block
  fp_add_inputs_t         fma_add_inputs;//add inputs from FMADD after MUL stage
  fp_unit_writeback_t     add_wb;
  unit_issue_interface add_issue();

  always_comb begin
    if (fma_mul_outputs_r.is_fma) begin 
      //FMA instruction in pipeline -> prioritized
      fp_add_inputs = fma_add_inputs;
      add_issue.id = fma_mul_wb.id;
      add_issue.new_request = fma_mul_wb.done & add_issue.ready;
      add_invalid_operation = 0;
      fp_add_grs = fma_mul_grs;
      expo_diff_to_add = fma_mul_outputs_r.expo_diff;
      swap = fma_mul_outputs_r.swap;
    end else begin
      fp_add_inputs = add_inputs_from_fifo.fp_add_inputs;
      add_issue.id = add_inputs_from_fifo.id;
      add_issue.new_request = fp_add_inputs_fifo.pop;//fp_add_inputs_fifo.valid; //issue if fifo not empty
      add_invalid_operation = fma_mul_invalid_operation; 
      fp_add_grs = 'b0;
      expo_diff_to_add = add_inputs_from_fifo.expo_diff;
      swap = add_inputs_from_fifo.swap;
    end
  end 

  fp_add_madd_fused ADD (
    .clk          (clk),
    .rst          (rst),
    .fma_mul_invalid_operation (add_invalid_operation),
    .fp_add_inputs(fp_add_inputs),
    .swap         (swap),
    .expo_diff_in (expo_diff_to_add),
    .fp_add_grs   (fp_add_grs),
    .issue        (add_issue),
    .fp_wb        (fp_madd_wb)
  );

  ////////////////////////////////////////////////////////
  //Ready
  assign issue.ready = mul_issue.ready & ~fp_add_inputs_fifo.full; //ready if fmul's first stage is empty and adder_fifo is not full
endmodule 




