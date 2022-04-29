import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module fp_cmp_simulation_wrapper (
  input clk,
  input rst,
  //inputs
  input logic [FLEN-1:0]    rs1,
  input logic [FLEN-1:0]    rs2,
  input logic [2:0]         fn3,
  //issue
  input logic possible_issue,
  input logic new_request,
  input logic new_request_r,
  input instruction_id_t instruction_id,
  output logic ready,
  //writeback
  output instruction_id_t id,
  output logic done,
  output logic [XLEN-1:0] rd,
  //fcsr
  output [4:0] fflags
  );

  fp_cmp_inputs_t fp_cmp_inputs;
  unit_issue_interface issue();
  unit_writeback_t wb; 

  fp_cmp fp_cmp(.clk          (clk),
                .rst          (rst),
                .fp_cmp_inputs(fp_cmp_inputs),
                .issue        (issue),
                .wb           (wb),
                .fflags       (fflags)
                );

  assign fp_cmp_inputs.rs1 = rs1;
  assign fp_cmp_inputs.rs2 = rs2;
  assign fp_cmp_inputs.fn3 = fn3;

  assign ready = issue.ready;
  assign issue.possible_issue = possible_issue;
  assign issue.new_request = new_request;
  assign issue.new_request_r = new_request_r;
  assign issue.instruction_id = instruction_id;

  assign id = wb.id;
  assign done = wb.done;
  assign rd = wb.rd;
endmodule