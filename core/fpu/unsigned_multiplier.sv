import taiga_config::*;
import taiga_types::*;
import l2_config_and_types::*;
import fpu_types::*;

module unsigned_multiplier #(parameter WIDTH = 53) (
  input logic clk,
  input logic rst,
  input logic advance1,
  input logic advance2,
  input logic [WIDTH-1:0] rs1,
  input logic [WIDTH-1:0] rs2,
  output logic [2*WIDTH-1:0] out
);

  logic [WIDTH-1:0] rs1_r, rs2_r;

  always_ff @ (posedge clk) begin
    if (advance1) begin
      rs1_r <= rs1;
      rs2_r <= rs2;
    end

    if (advance2) begin
      out <= rs1_r * rs2_r;
    end
  end

endmodule

