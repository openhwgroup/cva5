import taiga_config::*;
import taiga_types::*;
import l2_config_and_types::*;
import fpu_types::*;

module pre_normalize(
    input logic [FLEN-1:0] rs2,
    input logic rs2_hidden_bit,
    output logic [EXPO_WIDTH-1:0] left_shift_amt,
    output logic [FRAC_WIDTH:0] frac_normalized
);

  logic [EXPO_WIDTH-1:0] expo;
  logic [FRAC_WIDTH:0] frac;
  logic [EXPO_WIDTH-1:0] clz_with_prepended_0s;
  
  ////////////////////////////////////////////////////
  //Implementation
  //Unpack
  assign expo = rs2[FLEN-2-:EXPO_WIDTH];
  assign frac = {rs2_hidden_bit, rs2[FRAC_WIDTH-1:0]};

  //CLZ on subnormal input, and left shift to normalize
  //Assuming clz instances are optimized away when ENABLE_SUBNORMAL == 0
  generate if (FRAC_WIDTH+1 <= 32) begin
      clz frac_clz (
        .clz_input (32'(frac)),
        .clz (clz_with_prepended_0s[4:0])
      );
      assign left_shift_amt = clz_with_prepended_0s - (32 - (FRAC_WIDTH + 1));
  end else begin
      clz_tree frac_clz (
        .clz_input (64'(frac)),
        .clz (clz_with_prepended_0s[5:0])
      );
      assign left_shift_amt = clz_with_prepended_0s - (64 - (FRAC_WIDTH + 1));
  end endgenerate

  generate if (ENABLE_SUBNORMAL) 
    assign frac_normalized = frac << left_shift_amt;
  else
    assign frac_normalized = frac;
  endgenerate
  
endmodule
