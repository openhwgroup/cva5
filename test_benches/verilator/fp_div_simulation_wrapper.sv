import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module fp_div_simulation_wrapper (
  input clk,
  input rst,
  //inputs
  input logic [FLEN-1:0]    rs1,
  input logic [FLEN-1:0]    rs2,
  input logic [2:0]         rm,
  input id_t instruction_id,
  //
  input logic               gc_fetch_flush,
  //issue
  input logic               new_request,
  input logic               possible_issue,
  //writeback
  input logic ack,
  output logic done,
  output logic [FLEN-1:0]   rd,
  output id_t writeback_id,  
  //fcsr
  output [4:0] fflags
  );

  fp_unit_issue_interface issue();
  fp_div_sqrt_inputs_t fp_div_sqrt_inputs;
  fp_unit_writeback_interface fp_wb(); 
  int counter;
  always_ff @ (posedge clk) begin
    if (new_request)
      counter <= counter + 1;
  end

  assign issue.new_request = new_request;
  assign issue.possible_issue = possible_issue;
  assign issue.id = instruction_id;

  assign fp_div_sqrt_inputs.rs1 = rs1;
  assign fp_div_sqrt_inputs.rs2 = rs2;
  assign fp_div_sqrt_inputs.rm = rm;
  assign fp_div_sqrt_inputs.id = instruction_id;

  assign done = fp_wb.done;
  assign writeback_id = fp_wb.id;
  assign rd = fp_wb.rd;
  assign fp_wb.ack = ack;


  fp_div fp_div(
    .clk               (clk),
    .rst               (rst),
    //.gc_fetch_flush    ('0),
    .fp_div_sqrt_inputs(fp_div_sqrt_inputs),
    .issue             (issue),
    .div_wb            (fp_wb)
    );

endmodule
