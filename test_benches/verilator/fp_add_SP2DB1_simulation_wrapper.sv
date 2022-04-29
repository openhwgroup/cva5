import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module fp_add_mp_simulation_wrapper (
  input clk,
  input rst,
  //inputs
  input logic [FLEN-1:0]    rs1,
  input logic [FLEN-1:0]    rs2,
  input logic [6:0]         SP1_fn7,
  input logic [6:0]         SP2_fn7,
  input logic [6:0]         DB_fn7,
  input logic [2:0]         SP1_rm,
  input logic [2:0]         SP2_rm,
  input logic [2:0]         DB_rm,
  input logic               is_double,
  //issue
  input logic possible_issue,
  input logic new_request,
  input logic new_request_r,
  input fp_instruction_id_t instruction_id,
  output logic ready,
  //writeback
  output fp_instruction_id_t id,
  output logic done,
  output logic [FLEN-1:0] rd,
  //fcsr
  output [4:0] fflags
  );

  logic [2:0] SP1_rs1_grs = 3'b0;
  logic [2:0] SP2_rs1_grs = 3'b0;
  logic [2:0] DB_rs1_grs = 3'b0;
  fp_add_inputs_t fp_add_inputs;
  fp_unit_issue_interface issue();
  fp_unit_writeback_t fp_wb; 

  fp_add_mp fp_add (.*);

  assign fp_add_inputs.rs1 = rs1;
  assign fp_add_inputs.rs2 = rs2;
  assign fp_add_inputs.SP1_fn7 = SP1_fn7;
  assign fp_add_inputs.SP2_fn7 = SP2_fn7;
  assign fp_add_inputs.DB_fn7 =  DB_fn7;
  assign fp_add_inputs.SP1_rm = SP1_rm;
  assign fp_add_inputs.SP2_rm = SP2_rm;
  assign fp_add_inputs.DB_rm = DB_rm;
  assign fp_add_inputs.is_double = is_double;
  assign ready = issue.ready;
  assign issue.possible_issue = possible_issue;
  assign issue.new_request = new_request;
  assign issue.new_request_r = new_request_r;
  assign issue.instruction_id = instruction_id;

  assign id = fp_wb.id;
  assign done = fp_wb.done;
  assign rd = fp_wb.rd;
endmodule
