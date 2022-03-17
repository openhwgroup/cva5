import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module fp_special_case_detection_mp #(parameter FRAC_W=52, parameter EXPO_W=11) (
  input logic [FRAC_W+EXPO_W:0] input1,
  output logic is_inf,
  output logic is_SNaN,
  output logic is_QNaN,
  output logic is_zero
);

  localparam FPLEN = 1 + FRAC_W + EXPO_W;
  
  logic expo_all_1s = &input1[FPLEN-2-:EXPO_W];

  assign is_inf = expo_all_1s & ~(|input1[0+:FRAC_W]);
  assign is_SNaN = expo_all_1s & ~input1[FRAC_W-1] & input1[FRAC_W-2] & ~|input1[FRAC_W-3:0];
  assign is_QNaN = expo_all_1s & input1[FRAC_W-1] & ~|input1[FRAC_W-2:0];
  assign is_zero = ~|input1[FPLEN-2-:EXPO_W]; // subnormal considered zero

endmodule

module fp_special_case_detection_sandboxed #(parameter SANDBOX_FRAC_W=52, parameter SANDBOX_EXPO_W=11) (
  input logic [FLEN-1:0] data_in,
  output logic is_inf,
  output logic is_SNaN,
  output logic is_QNaN,
  output logic is_zero,
  output logic hidden
);

  logic sign_in;
  logic [EXPO_WIDTH-1:0] expo_in;
  logic [FRAC_WIDTH-1:0] frac_in;
  logic sign_sandboxed;
  logic [SANDBOX_EXPO_W-1:0] expo_sandboxed;
  logic [SANDBOX_FRAC_W-1:0] frac_sandboxed;

  //unpack
  assign {sign_in, expo_in, frac_in} = data_in;
  assign sign_sandboxed = sign_in;
  assign expo_sandboxed = expo_in[SANDBOX_EXPO_W-1:0];
  assign frac_sandboxed = frac_in[FRAC_WIDTH-1-:SANDBOX_FRAC_W];
  generate if (ENABLE_SUBNORMAL)
    assign hidden = |expo_sandboxed;
  else
    assign hidden = 1;
  endgenerate 

  //process
  logic expo_all_1s = &expo_sandboxed;
  logic frac_lower_all_0s = ~(|frac_sandboxed[SANDBOX_FRAC_W-3:0]);

  assign is_inf = expo_all_1s & ~(|frac_sandboxed);
  assign is_SNaN = expo_all_1s & ~frac_sandboxed[SANDBOX_FRAC_W-1] & frac_sandboxed[SANDBOX_FRAC_W-2] & frac_lower_all_0s;
  assign is_QNaN = expo_all_1s & ~frac_sandboxed[SANDBOX_FRAC_W-1] & frac_sandboxed[SANDBOX_FRAC_W-2] & frac_lower_all_0s;
  assign is_zero = ~(|expo_sandboxed) & ~frac_sandboxed[SANDBOX_FRAC_W-1] & ~frac_sandboxed[SANDBOX_FRAC_W-2] & frac_lower_all_0s;

endmodule 









