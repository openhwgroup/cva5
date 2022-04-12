import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module fp_div(
  input logic                   clk,
  input logic                   rst,
  input fp_div_sqrt_inputs_t    fp_div_sqrt_inputs,
  unit_issue_interface.unit  issue,
  fp_unit_writeback_interface.unit div_wb
  );

  logic                         running;
  logic                         start_algorithm;
  fp_div_sqrt_inputs_t          div_op_attr;
  fp_div_sqrt_inputs_t          in_progress_attr;
  logic                         done;
  logic [4:0]                   fflags;

  //input buffer
  fifo_interface #(.DATA_WIDTH($bits(fp_div_sqrt_inputs_t))) input_fifo();
  taiga_fifo #(.DATA_WIDTH($bits(fp_div_sqrt_inputs_t)), .FIFO_DEPTH(1))
    fp_div_input_fifo (.clk(clk),
                       .rst(rst),
                       .fifo(input_fifo)
                      );

  assign input_fifo.data_in = fp_div_sqrt_inputs;
  assign input_fifo.push = issue.new_request;
  assign input_fifo.potential_push = issue.new_request;
  assign input_fifo.pop = input_fifo.valid & (~running); //fp_wb.done;
  assign issue.ready = ~input_fifo.full | input_fifo.pop;
  assign div_op_attr = input_fifo.data_out;

  assign start_algorithm = input_fifo.valid & (~running);
  always_ff @ (posedge clk) begin
    if (input_fifo.pop)
      in_progress_attr <= div_op_attr;
  end

  set_clr_reg_with_rst #(.SET_OVER_CLR(1), .WIDTH(1), .RST_VALUE('0)) in_progress_m (
      .clk, .rst,
      .set(input_fifo.valid & (~running)),
      .clr(div_wb.ack),
      .result(running)
    );

  fp_div_core fp_div_core_inst (
    .clk               (clk),
    .rst               (rst),
    .start_algorithm   (start_algorithm),
    .fp_div_sqrt_inputs(div_op_attr),
    .fp_wb             (div_wb)
  );
endmodule : fp_div
