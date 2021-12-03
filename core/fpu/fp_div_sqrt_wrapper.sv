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
  assign wb.rd = div_wb.done ? div_wb.rd : sqrt_wb.rd;
  assign wb.id = div_wb.done ? div_wb.id : sqrt_wb.id;
  assign wb.done = div_wb.done | sqrt_wb.done;
  assign wb.fflags = div_wb.done ? div_wb.fflags : sqrt_wb.fflags;
  assign wb.hidden = div_wb.done ? div_wb.hidden : sqrt_wb.hidden;
  assign wb.grs = div_wb.done ? div_wb.grs : sqrt_wb.grs;
  assign wb.clz = div_wb.done ? div_wb.clz : sqrt_wb.clz;
  assign wb.rm = div_wb.done ? div_wb.rm : sqrt_wb.rm;
  assign div_wb.ack = wb.ack;
  assign sqrt_wb.ack = wb.ack;
 
endmodule


