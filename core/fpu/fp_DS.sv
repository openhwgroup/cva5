import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module fp_DS (
  input logic clk,
  input logic advance,
  input logic [FLEN-1:0]     rs1_fp,
  input logic [3:0] rs1_special_case,
  input logic is_D2S,
  output logic [FLEN-1:0] rd,
  output logic [2:0] grs
  );

  //////////////////////////////////
  //DS Conversion
  localparam SINGLE_BIAS = 127;
  localparam DOUBLE_BIAS = 1023;
  localparam EXPO_WIDTH_SINGLE = 8;
  localparam FRAC_WIDTH_SINGLE = 23;

  //////////////////////////////////
  //Single Precision to Double Precision
  
  //special_case
  logic is_inf_S, is_SNaN_S, is_QNaN_S, is_zero_S; 
  fp_special_case_detection_mp #(.FRAC_W(FRAC_WIDTH_SINGLE), .EXPO_W(EXPO_WIDTH_SINGLE)) special_case_S (
    .input1(rs1_S),
    .is_inf(is_inf_S),
    .is_SNaN(is_SNaN_S),
    .is_QNaN(is_QNaN_S),
    .is_zero(is_zero_S)
  );

  logic [31:0] rs1_S;
  logic rs1_sign_S;
  logic [EXPO_WIDTH-1:0] rs1_expo_S;
  logic [FRAC_WIDTH-1:0] rs1_frac_S;
  logic result_sign_D[1:0];
  logic [EXPO_WIDTH-1:0] result_expo_D[1:0];
  logic [FRAC_WIDTH-1:0] result_frac_D[1:0];
  logic [2:0] result_grs_D[1:0];
  assign rs1_S = rs1_fp[0+:32];
  assign rs1_sign_S = rs1_fp[31];
  assign rs1_expo_S = EXPO_WIDTH'(rs1_S[30-:EXPO_WIDTH_SINGLE]);
  assign rs1_frac_S = FRAC_WIDTH'(rs1_S[0+:FRAC_WIDTH_SINGLE]);
  assign result_sign_D[0] = rs1_sign_S;
  assign result_expo_D[0] = rs1_expo_S - SINGLE_BIAS + DOUBLE_BIAS;
  assign result_frac_D[0] = {rs1_frac_S[0+:FRAC_WIDTH_SINGLE], (FRAC_WIDTH-FRAC_WIDTH_SINGLE)'(0)};

  //////////////////////////////////
  //Double Precision to Single Precision

  //special case
  logic is_inf_D, is_SNaN_D, is_QNaN_D, is_zero_D; 
  assign {is_inf_D, is_SNaN_D, is_QNaN_D, is_zero_D} = rs1_special_case;
  //fp_special_case_detection_mp #(.FRAC_W(FRAC_WIDTH), .EXPO_W(EXPO_WIDTH)) special_case_D (
    //.input1(rs1_fp),
    //.is_inf(is_inf_D),
    //.is_SNaN(is_SNaN_D),
    //.is_QNaN(is_QNaN_D),
    //.is_zero(is_zero_D)
  //);

  logic [FLEN-1:0] rs1_D;
  logic rs1_sign_D;
  logic [EXPO_WIDTH-1:0] rs1_expo_D;
  logic [FRAC_WIDTH-1:0] rs1_frac_D;
  logic result_sign_S[1:0];
  logic [EXPO_WIDTH-1:0] result_expo_S[1:0];
  logic [FRAC_WIDTH_SINGLE-1:0] result_frac_S[1:0];
  logic [FRAC_WIDTH-FRAC_WIDTH_SINGLE-1:0] residual_bits;
  logic [2:0] result_grs_S[1:0];

  assign rs1_D = rs1_fp;
  assign rs1_sign_D = rs1_D[FLEN-1];
  assign rs1_expo_D = rs1_D[FLEN-2-:EXPO_WIDTH];
  assign rs1_frac_D = rs1_D[0+:FRAC_WIDTH];
  assign result_sign_S[0] = rs1_sign_D;
  assign result_expo_S[0] = rs1_expo_D - DOUBLE_BIAS + SINGLE_BIAS;
  assign {result_frac_S[0], residual_bits} = rs1_frac_D;//[FRAC_WIDTH-1-:FRAC_WIDTH_SINGLE];
  assign result_grs_S[0] = {residual_bits[FRAC_WIDTH-FRAC_WIDTH_SINGLE-1-:2], |residual_bits[FRAC_WIDTH-FRAC_WIDTH_SINGLE-3:0]};

  ////////////////////////////////////
  //NAN Box and output
  logic is_D2S_r;
  always_comb begin
    if (is_D2S_r) begin
      //sign = result_sign_S[1];
      //expo = {{(EXPO_WIDTH-EXPO_WIDTH_SINGLE){1'b0}}, result_expo_S[1][0+:EXPO_WIDTH_SINGLE]};
      //frac = {{(FRAC_WIDTH-FRAC_WIDTH_SINGLE){1'b0}}, result_frac_S[1][0+:FRAC_WIDTH_SINGLE]};
      grs = result_grs_S[1];
      rd = {{(FLEN-XLEN){1'b1}}, result_sign_S[1], result_expo_S[1][EXPO_WIDTH_SINGLE-1:0], result_frac_S[1][FRAC_WIDTH_SINGLE-1:0]};
    end else begin
      //sign = result_sign_D[1];
      //expo = result_expo_D[1];
      //frac = result_frac_D[1];
      grs = result_grs_D[1];
      rd = {result_sign_D[1], result_expo_D[1], result_frac_D[1]};
    end
  end

  always_ff @ (posedge clk) begin
    if(advance) begin
      result_sign_S[1] <= result_sign_S[0];  
      if (is_inf_D) begin
        result_expo_S[1] <= '1;
        result_frac_S[1] <= '0;
        result_grs_S[1] <= '0;
      end else if (is_zero_D) begin
        result_expo_S[1] <= '0;
        result_frac_S[1] <= '0;        
        result_grs_S[1] <= '0;
      end else begin
        result_expo_S[1] <= result_expo_S[0]; 
        result_frac_S[1] <= result_frac_S[0];
        result_grs_S[1] <= result_grs_S[0];
      end

      result_sign_D[1] <= result_sign_D[0];  
      if (is_inf_S) begin
        result_expo_D[1] <= '1;
        result_frac_D[1] <= '0;
        result_grs_D[1] <= '0;
      end else if (is_zero_S) begin
        result_expo_D[1] <= '0;
        result_frac_D[1] <= '0;        
        result_grs_D[1] <= '0;
      end else if (is_SNaN_S | is_QNaN_S) begin
        result_expo_D[1] <= '1;
        result_frac_D[1] <= result_frac_D[0];        
        result_grs_D[1] <= '0;
      end else begin
        result_expo_D[1] <= result_expo_D[0]; 
        result_frac_D[1] <= result_frac_D[0];
        result_grs_D[1] <= result_grs_D[0];
      end

      is_D2S_r <= is_D2S;
    end
  end

endmodule


