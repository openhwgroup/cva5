import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module fp_new_cvt_simulation_wrapper (
  input clk,
  input rst,
  //inputs
  input logic [FLEN-1:0]    f2i_rs1,
  input logic [XLEN-1:0]    i2f_rs1,
  input logic [2:0]         rm,
  input logic               is_mv,
  input logic               is_signed,
  input logic               is_float,
  //issue
  input logic possible_issue,
  input logic fp_possible_issue,
  input logic new_request,
  input logic fp_new_request,
  input fp_instruction_id_t fp_instruction_id,
  input instruction_id_t instruction_id,
  output logic ready,
  output logic fp_ready,
  //writeback
  output fp_instruction_id_t fp_id,
  output instruction_id_t id,
  output logic done,
  output logic fp_done,
  output logic [XLEN-1:0] rd,
  output logic [FLEN-1:0] fp_rd,
  //fcsr
  output [4:0] fflags
  );

  fp_cvt_mv_inputs_t fp_cvt_mv_inputs;
  fp_unit_issue_interface fp_issue();
  unit_issue_interface issue();
  fp_unit_writeback_t fp_wb; 
  unit_writeback_t wb;

  fp_cvt_top DUT (
              .clk             (clk),
              .rst             (rst),
              .fp_cvt_mv_inputs(fp_cvt_mv_inputs),
              .fp_issue        (fp_issue),
              .issue           (issue),
              .fp_wb           (fp_wb),
              .wb              (wb),
              .fflags          (fflags)
              );

  assign fp_cvt_mv_inputs.f2i_rs1 = f2i_rs1;
  assign fp_cvt_mv_inputs.i2f_rs1 = i2f_rs1;
  assign fp_cvt_mv_inputs.rm = rm;
  assign fp_cvt_mv_inputs.is_mv = is_mv;
  assign fp_cvt_mv_inputs.is_float = is_float;
  assign fp_cvt_mv_inputs.is_signed = is_signed;

  assign ready = issue.ready;
  assign issue.new_request = new_request;
  assign issue.instruction_id = instruction_id;

  assign fp_ready = fp_issue.ready;
  assign fp_issue.new_request = fp_new_request;
  assign fp_issue.instruction_id = fp_instruction_id;

  assign fp_id = fp_wb.id;
  assign id = wb.id;
  assign fp_done = fp_wb.done;

  assign done = wb.done;
  assign fp_rd = fp_wb.rd;
  assign rd = wb.rd;
endmodule