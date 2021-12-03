import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module fp_f2i (
  input logic clk,
  input logic rst,
  input logic advance,
  input logic new_request,
  input id_t id,
  input logic [FLEN-1:0]     rs1_fp,
  input logic hidden_bit_i,
  input logic[3:0] special_case,
  input logic is_signed,
  output logic [XLEN-1:0]  f2i_int_abs,
  output logic result_sign,
  output logic [2:0] grs,
  output logic done,
  output id_t f2i_id,
  output logic invalid_operationFlg
  );

  logic is_signed_r;
  logic rs1_sign [1:0];
  logic [EXPO_WIDTH-1:0] rs1_expo [1:0];
  logic overflow;
  logic overflow_r;
  logic [EXPO_WIDTH-1:0] rs1_expo_unbiased;
  logic [EXPO_WIDTH-1:0] rs1_expo_unbiased_r; 
  logic rs1_hidden_bit [1:0];
  logic [FRAC_WIDTH-1:0] rs1_frac [1:0];
  logic rs1_NaN[1:0];
  logic rs1_zero;
  logic rs1_inf[1:0];
  logic larger_than_unsigned_max, larger_than_unsigned_max_r;
  logic smaller_than_unsigned_min, smaller_than_unsigned_min_r;
  logic larger_than_signed_max, larger_than_signed_max_r;
  logic smaller_than_signed_min, smaller_than_signed_min_r;
  logic [XLEN-1:0] rs1_int_abs, unsigned_special_output, signed_special_output;
  logic [EXPO_WIDTH-1:0]  shift_amt;
  logic [XLEN+FRAC_WIDTH-1:0] rs1_int_dot_frac; 
  logic invalid_operationExp;
  logic [2:0] f2i_grs;

  //pre processing
  assign rs1_hidden_bit[0] = hidden_bit_i;//~(rs1_expo[0] == '0);
  assign rs1_inf[0] = special_case[3];//(rs1_expo[0] == '1) && (rs1_frac[0][FRAC_WIDTH-1:0] == '0);
  assign rs1_NaN[0] = |special_case[2:1];//(rs1_expo[0] == '1) && (rs1_frac[0][FRAC_WIDTH-1:0] != '0);
  assign rs1_sign[0] = rs1_fp[FLEN-1];
  assign rs1_expo[0] = rs1_fp[FLEN-2-:EXPO_WIDTH];
  assign rs1_frac[0] = rs1_fp[FRAC_WIDTH-1:0];
  assign {overflow, rs1_expo_unbiased} = rs1_expo[0] - BIAS;
  assign larger_than_unsigned_max = ($signed(rs1_expo_unbiased) >= XLEN);
  assign smaller_than_unsigned_min = (rs1_sign[0] == 1) && (rs1_expo[0] != '0) && (rs1_frac[0] != 0);  // negative float that is not -0
  assign larger_than_signed_max = ($signed(rs1_expo_unbiased) >= (XLEN - 1));
  assign smaller_than_signed_min = (rs1_sign[0] == 1) && ($signed(rs1_expo_unbiased) >= (XLEN - 1));
  assign invalid_operationExp = rs1_inf[0] || rs1_NaN[0] || (is_signed && (larger_than_signed_max || smaller_than_signed_min)) || 
                                                      (!is_signed && (larger_than_unsigned_max || smaller_than_unsigned_min));
  //left shift amount cannot exceed 31 
  //TODO: optimize this
  //assign shift_amt = (rs1_expo[1] - BIAS > (XLEN-1)) ? (XLEN-1) : (rs1_expo[1] - BIAS); 
  assign shift_amt = (rs1_expo_unbiased_r > (XLEN-1)) ? (XLEN-1) : (rs1_expo_unbiased_r); 
  assign rs1_int_dot_frac = {{(XLEN-1){1'b0}}, rs1_hidden_bit[1], rs1_frac[1]} << shift_amt;
  
  always_comb begin 
    //if (rs1_expo[1] < BIAS) begin 
    if (overflow_r) begin 
      //abs(rs1_fp) < 1.0
      rs1_int_abs = 0;
      f2i_grs = (BIAS-rs1_expo[1]) > 1 ? {2'b0, |rs1_frac[1]} : {rs1_hidden_bit[1], rs1_frac[1][(FRAC_WIDTH-1)-:2]}; //hidden has to be one and cannot be right shifted more than onece to round up 
    end else begin 
       rs1_int_abs = rs1_int_dot_frac[(XLEN+FRAC_WIDTH-1)-:XLEN];
       f2i_grs = {rs1_int_dot_frac[(FRAC_WIDTH-1)-:2], |rs1_int_dot_frac[0+:FRAC_WIDTH-2]};
    end
  end

  //registers
  always_ff @ (posedge clk) begin 
    if (advance) begin 
      done <= new_request;
      f2i_id <= id;

      rs1_hidden_bit[1] = rs1_hidden_bit[0];
      rs1_sign[1] <= rs1_sign[0];
      rs1_expo[1] <= rs1_expo[0];
      rs1_frac[1] <= rs1_frac[0]; 
      rs1_inf[1] <= rs1_inf[0];
      rs1_NaN[1] <= rs1_NaN[0];
      is_signed_r <= is_signed;
      invalid_operationFlg <= invalid_operationExp; 
      larger_than_unsigned_max_r <= larger_than_unsigned_max;
      larger_than_signed_max_r <= larger_than_signed_max; 
      smaller_than_unsigned_min_r <= smaller_than_unsigned_min;
      smaller_than_signed_min_r <= smaller_than_signed_min;

      rs1_expo_unbiased_r <= rs1_expo_unbiased;
      overflow_r <= overflow;
    end
  end

  always_comb begin
    if ((~rs1_sign[1] & rs1_inf[1]) | rs1_NaN[1] | larger_than_unsigned_max_r)
      unsigned_special_output = 32'hffffffff;
    else //((rs1_sign[1] & rs1_inf[1]) | smaller_than_unsigned_min_r)
      unsigned_special_output = '0;
  end

  always_comb begin
    if ((~rs1_sign[1] & rs1_inf[1]) | rs1_NaN[1] | larger_than_signed_max_r)
      signed_special_output = 32'h7fffffff;
    else //((rs1_sign[1] & rs1_inf[1]) | smaller_than_signed_min_r)
      signed_special_output = 32'h80000000;
  end

  assign f2i_int_abs = invalid_operationFlg ? (is_signed_r ? signed_special_output : unsigned_special_output) : rs1_int_abs; //IEEE doesn't specify default handling of invalidOp exception
  assign grs = invalid_operationFlg ? '0 : f2i_grs;
  assign result_sign = rs1_sign[1];
endmodule : fp_f2i
