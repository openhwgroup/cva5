import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module fp_sign_inj_simulation_wrapper (
  input clk,
  input rst,
  //inputs
  input logic [FLEN-1:0]    rs1,
  input logic               rs2_sign,
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
  output logic [FLEN-1:0] rd
  );

  fp_sign_inject_inputs_t fp_sign_inj_inputs;
  fp_unit_issue_interface issue();
  fp_unit_writeback_t fp_wb; 

  fp_sign_inj fp_sign_inj(.clk          (clk),
                          .rst          (rst),
                          .fp_sign_inj_inputs(fp_sign_inj_inputs),
                          .issue        (issue),
                          .fp_wb        (fp_wb)
                          );

  assign fp_sign_inj_inputs.rs1 = rs1;
  assign fp_sign_inj_inputs.rs2_sign = rs2_sign;
  assign fp_sign_inj_inputs.rm = rm;

  assign ready = issue.ready;
  assign issue.possible_issue = possible_issue;
  assign issue.new_request = new_request;
  assign issue.new_request_r = new_request_r;
  assign issue.instruction_id = instruction_id;

  assign id = fp_wb.id;
  assign done = fp_wb.done;
  assign rd = fp_wb.rd;
endmodule