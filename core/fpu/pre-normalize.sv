import taiga_config::*;
import taiga_types::*;
import l2_config_and_types::*;
import fpu_types::*;

module pre_normalize #(
  parameter WIDTH=FRAC_WIDTH+1
)(
    input logic [FLEN-1:0] rs2,
    input logic rs2_hidden_bit,
    input logic enable,
    output logic [EXPO_WIDTH-1:0] pre_normalize_shift_amt,
    output logic [WIDTH-1:0] frac_normalized
);

  logic [EXPO_WIDTH-1:0] expo;
  logic [WIDTH-1:0] frac;
  logic [EXPO_WIDTH-1:0] clz_with_prepended_0s;
  
  ////////////////////////////////////////////////////
  //Implementation
  //Unpack
  assign expo = rs2[FLEN-2-:EXPO_WIDTH];
  assign frac = {{(WIDTH-(FRAC_WIDTH+1)){1'b0}}, rs2_hidden_bit, rs2[FRAC_WIDTH-1:0]}; 
  logic [EXPO_WIDTH-1:0] debug1, debug2;

  //CLZ on subnormal input, and left shift to normalize
  //Assuming clz instances are optimized away when ENABLE_SUBNORMAL == 0
  generate if (FRAC_WIDTH+1 <= 32) begin
      localparam CLZ_OFFSET = (32 - (FRAC_WIDTH + 1));
      clz frac_clz (
        .clz_input (32'(frac)),
        .clz (clz_with_prepended_0s[4:0])
      );
      assign pre_normalize_shift_amt = clz_with_prepended_0s & {EXPO_WIDTH{enable}} - (CLZ_OFFSET & {EXPO_WIDTH{enable}});
  end else begin
      localparam CLZ_OFFSET = (64 - (FRAC_WIDTH + 1));
      clz_tree frac_clz (
        .clz_input (64'(frac)),
        .clz (clz_with_prepended_0s[5:0])
      );
      assign pre_normalize_shift_amt = (clz_with_prepended_0s & {EXPO_WIDTH{enable}}) - (CLZ_OFFSET & {EXPO_WIDTH{enable}});
  end endgenerate

  generate if (ENABLE_SUBNORMAL) begin
    assign frac_normalized = frac << pre_normalize_shift_amt;
  end else begin
    assign frac_normalized = frac;
  end
  endgenerate

  function logic [EXPO_WIDTH-1:0] getMin(input logic [EXPO_WIDTH-1:0] x, y);
    getMin = x > y ? y : x;
  endfunction
  
endmodule
