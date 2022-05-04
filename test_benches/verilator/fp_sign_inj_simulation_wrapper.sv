import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module fp_sign_inj_simulation_wrapper (
  input clk,
  input rst,
  //inputs
  input logic [FLEN-1:0]    rs1,
  input logic [FLEN-1:0]    rs2,
  input logic [2:0]         rm,
  input logic hidden,
  //issue
  input logic possible_issue,
  input logic new_request,
  input logic new_request_r,
  input id_t instruction_id,
  output logic ready,
  //writeback
  output id_t id,
  output logic done,
  output logic [FLEN-1:0] rd
  );

  fp_sign_inject_inputs_t fp_sign_inject_inputs;
  unit_issue_interface issue();
  fp_unit_writeback_interface fp_wb();

  fp_sign_inj fp_sign_inj_inst(.clk          (clk),
                               .advance      (1),
                               .issue        (issue),
                               .fp_sign_inject_inputs(fp_sign_inject_inputs),
                               .wb        (fp_wb)
                          );

  assign fp_sign_inject_inputs.rs1 = rs1;
  assign fp_sign_inject_inputs.rs2_sign = rs2[FLEN-1];
  assign fp_sign_inject_inputs.rs1_hidden_bit = hidden;
  assign fp_sign_inject_inputs.rm = rm;

  assign ready = 1;//issue.ready;
  assign issue.possible_issue = possible_issue;
  assign issue.new_request = new_request;
  assign issue.new_request_r = new_request_r;
  assign issue.id = instruction_id;

  assign id = fp_wb.id;
  assign done = fp_wb.done;
  assign rd = fp_wb.rd;
  assign fp_wb.ack = 1;
endmodule
