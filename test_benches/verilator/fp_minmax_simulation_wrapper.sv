import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module fp_minmax_simulation_wrapper (
  input clk,
  input rst,
  //inputs
  input logic [FLEN-1:0]    rs1,
  input logic [FLEN-1:0]    rs2,
  input logic [2:0]         rm,
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

  fp_minmax_inputs_t fp_minmax_inputs;
  fp_unit_issue_interface issue();
  fp_unit_writeback_t wb; 

  fp_minmax fp_minmax(.clk          (clk),
                .rst          (rst),
                .fp_minmax_inputs(fp_minmax_inputs),
                .issue        (issue),
                .fp_wb           (wb),
                .fflags       (fflags)
                );

  assign fp_minmax_inputs.rs1 = rs1;
  assign fp_minmax_inputs.rs2 = rs2;
  assign fp_minmax_inputs.rm = rm;

  assign ready = issue.ready;
  assign issue.possible_issue = possible_issue;
  assign issue.new_request = new_request;
  assign issue.new_request_r = new_request_r;
  assign issue.instruction_id = instruction_id;

  assign id = wb.id;
  assign done = wb.done;
  assign rd = wb.rd;
endmodule