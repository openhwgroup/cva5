import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module fp_div_core_simulation_wrapper (
  input clk,
  input rst,
  //inputs
  input logic [FLEN-1:0]    rs1,
  input logic [FLEN-1:0]    rs2,
  input logic [2:0]         rm,
  //issue
  input logic start,
  //writeback
  output logic done,
  output logic [FLEN-1:0] rd,
  input logic ack,
  //fcsr
  output [4:0] fflags
  );

  fp_div_sqrt_inputs_t fp_div_sqrt_inputs;
  fp_unit_writeback_t fp_wb; 

  fp_div_core fp_div(
    .clk               (clk),
    .rst               (rst),
    .start_algorithm   (start),
    .fp_div_sqrt_inputs(fp_div_sqrt_inputs),
    .fp_wb             (fp_wb)
    );

  assign fp_div_sqrt_inputs.rs1 = rs1;
  assign fp_div_sqrt_inputs.rs2 = rs2;
  assign fp_div_sqrt_inputs.rm = rm;

  assign done = fp_wb.done;
  assign rd = fp_wb.rd;
  assign fflags = fp_wb.fflags;

endmodule
