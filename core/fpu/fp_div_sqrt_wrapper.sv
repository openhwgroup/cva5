import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module fp_div_sqrt_wrapper(
  input logic                   clk,
  input logic                   rst,
  input fp_div_sqrt_inputs_t    fp_div_sqrt_inputs,
  unit_issue_interface.unit  issue,
  fp_unit_writeback_interface.unit wb
  );

  unit_issue_interface div_issue(), sqrt_issue();
  fp_unit_writeback_interface div_wb(), sqrt_wb();
  
  fp_sqrt sqrt(
    .clk (clk),
    .rst (rst),
    .issue (sqrt_issue),
    .fp_div_sqrt_inputs (fp_div_sqrt_inputs),
    .wb (sqrt_wb)
  );

  fp_div div(
    .clk (clk),
    .rst (rst),
    .issue (div_issue),
    .fp_div_sqrt_inputs (fp_div_sqrt_inputs),
    .div_wb (div_wb)
  );


  assign issue.ready = div_issue.ready & sqrt_issue.ready;
  assign div_issue.id = issue.id;
  assign sqrt_issue.id = issue.id;
  assign div_issue.new_request = issue.new_request & ~fp_div_sqrt_inputs.fn7[5];
  assign sqrt_issue.new_request = issue.new_request & fp_div_sqrt_inputs.fn7[5];
  assign div_issue.possible_issue = issue.possible_issue;
  assign sqrt_issue.possible_issue = issue.possible_issue;

  always_comb begin
    div_wb.ack = wb.ack & div_wb.done;
    sqrt_wb.ack = wb.ack & sqrt_wb.done;
    if (div_wb.done) begin
      wb.rd = div_wb.rd;
      wb.id = div_wb.id;
      wb.done = div_wb.done;
      wb.fflags = div_wb.fflags;
      wb.hidden = div_wb.hidden;
      wb.grs = div_wb.grs;
      wb.clz = div_wb.clz;
      wb.rm = div_wb.rm;
      wb.expo_overflow = div_wb.expo_overflow;
      wb.subnormal = div_wb.subnormal;
      wb.right_shift = div_wb.right_shift;
      wb.right_shift_amt = div_wb.right_shift_amt;
    end else begin
      wb.rd = sqrt_wb.rd;
      wb.id = sqrt_wb.id;
      wb.done = sqrt_wb.done;
      wb.fflags = sqrt_wb.fflags;
      wb.hidden = sqrt_wb.hidden;
      wb.grs = sqrt_wb.grs;
      wb.clz = sqrt_wb.clz;
      wb.rm = sqrt_wb.rm;
      wb.expo_overflow = sqrt_wb.expo_overflow;
      wb.subnormal = sqrt_wb.subnormal;
      wb.right_shift = sqrt_wb.right_shift;
      wb.right_shift_amt = sqrt_wb.right_shift_amt;
    end
  end
endmodule


