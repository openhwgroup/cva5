import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module fp_sign_inj (
  input logic clk,
  input logic rst,
  input fp_sign_inject_inputs_t fp_sign_inject_inputs,
  fp_unit_issue_interface.unit issue,
  fp_unit_writeback_interface fp_wb
  // output [4:0] fflags
);
  
  logic [FLEN-1:0]          rs1;
  logic                     rs2_sign;
  logic [2:0]               rm;
  logic                     done;
  id_t                      id;

  always_ff @ (posedge clk) begin 
    if (advance) begin
      rs1 <= fp_sign_inject_inputs.rs1;
      rs2_sign <= fp_sign_inject_inputs.rs2_sign;
      rm <= fp_sign_inject_inputs.rm;
      done <= issue.new_request;
      id <= issue.id;
    end else begin
      rs1 <= rs1;
      rs2_sign <= rs2_sign;
      rm <= rm;
      done <= done;
      id <= id;
    end
  end

  logic done_r;
  always_ff @ (posedge clk) begin
    if (fp_wb.ack)
      done_r <= 0;
    else if (done)
      done_r <= 1;
  end

  always_comb begin 
    case(rm)
      default: fp_wb.rd = {rs2_sign, rs1[FLEN-2:0]};
      3'b001: fp_wb.rd = {~rs2_sign, rs1[FLEN-2:0]};
      3'b010: fp_wb.rd = {rs2_sign ^ rs1[FLEN-1], rs1[FLEN-2:0]};
    endcase // rm
  end

  logic advance;
  assign advance = fp_wb.ack | ~fp_wb.done;
  assign fp_wb.done = done;
  assign fp_wb.id = id;
  assign fp_wb.fflags = '0;
  assign issue.ready = advance;

endmodule
