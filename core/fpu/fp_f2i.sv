import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module fp_f2i (
  input logic clk,
  input logic advance,
  unit_issue_interface.unit issue,
  input fp_f2i_inputs_t fp_f2i_inputs,
  unit_writeback_interface.unit wb
);

  logic is_signed, is_signed_r;
  logic [2:0] rm[2:0];
  logic rs1_sign [2:0];
  logic result_sign, result_sign_r;
  logic [EXPO_WIDTH-1:0] rs1_expo [1:0];
  logic overflow;
  logic overflow_r;
  logic [EXPO_WIDTH-1:0] rs1_expo_unbiased;
  logic [EXPO_WIDTH-1:0] rs1_expo_unbiased_r; 
  logic rs1_hidden_bit [1:0];
  logic [FRAC_WIDTH-1:0] rs1_frac [1:0];
  logic rs1_NaN[1:0];
  logic rs1_inf[1:0];
  logic rs1_zero[1:0];
  logic larger_than_unsigned_max, larger_than_unsigned_max_r;
  logic smaller_than_unsigned_min, smaller_than_unsigned_min_r;
  logic larger_than_signed_max, larger_than_signed_max_r;
  logic smaller_than_signed_min, smaller_than_signed_min_r;
  logic [XLEN-1:0] rs1_int_abs, unsigned_special_output, signed_special_output;
  logic [XLEN-1:0] f2i_int_abs, f2i_int_abs_r;
  logic [EXPO_WIDTH-1:0]  shift_amt;
  logic [XLEN+FRAC_WIDTH-1:0] rs1_int_dot_frac; 
  logic invalid_operationExp;
  logic invalid_operationFlg, invalid_operationFlg_r;
  logic roundup;
  logic [FLEN-1:0] result_if_overflow;
  logic [2:0] f2i_grs;
  logic [2:0] grs, grs_r;
  logic done, done_r;
  id_t id, id_r;

  ////////////////////////////////////////////////////
  //Implementation
  //pre processing
  assign rs1_hidden_bit[0] = fp_f2i_inputs.f2i_rs1_hidden;
  assign rs1_inf[0] = fp_f2i_inputs.f2i_rs1_special_case[3];
  assign rs1_NaN[0] = |fp_f2i_inputs.f2i_rs1_special_case[2:1];
  assign rs1_zero[0] = fp_f2i_inputs.f2i_rs1_special_case[0];
  assign rs1_sign[0] = fp_f2i_inputs.f2i_rs1[FLEN-1];
  assign rs1_expo[0] = fp_f2i_inputs.f2i_rs1[FLEN-2-:EXPO_WIDTH];
  assign rs1_frac[0] = fp_f2i_inputs.f2i_rs1[FRAC_WIDTH-1:0];
  assign rm[0] = fp_f2i_inputs.rm;
  assign is_signed = fp_f2i_inputs.is_signed;

  assign {overflow, rs1_expo_unbiased} = rs1_expo[0] - BIAS;
  assign larger_than_unsigned_max = ($signed(rs1_expo_unbiased) >= XLEN);
  assign smaller_than_unsigned_min = (rs1_sign[0]) & (~rs1_zero[0]);  // negative float that is not -0

  assign larger_than_signed_max = (~rs1_sign[0]) & ($signed(rs1_expo_unbiased) >= (XLEN - 1));
  assign smaller_than_signed_min = (rs1_sign[0]) & ($signed(rs1_expo_unbiased) >= (XLEN - 1));
  assign invalid_operationExp = rs1_inf[0] || rs1_NaN[0] || (is_signed && (larger_than_signed_max || smaller_than_signed_min)) || 
                                                      (!is_signed && (larger_than_unsigned_max || smaller_than_unsigned_min));
  //left shift amount cannot exceed 31 
  //TODO: optimize this
  //assign shift_amt = (rs1_expo[1] - BIAS > (XLEN-1)) ? (XLEN-1) : (rs1_expo[1] - BIAS); 
  assign shift_amt = (rs1_expo_unbiased_r > (XLEN-1)) ? (XLEN-1) : (rs1_expo_unbiased_r); 
  assign rs1_int_dot_frac = {{(XLEN-1){1'b0}}, rs1_hidden_bit[1], rs1_frac[1]} << shift_amt;

  //Special Case Output
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

  assign f2i_int_abs = invalid_operationFlg ? (is_signed_r ? signed_special_output : unsigned_special_output) : rs1_int_abs; //IEEE doesn't specify default handling of invalidOp exception
  assign grs = invalid_operationFlg ? '0 : f2i_grs;
  assign result_sign = rs1_sign[1]; //& is_signed_r;

  ////////////////////////////////////////////////////
  //Rounding
  fp_round_simplified round(
    .sign(result_sign_r),
    .rm(rm[2]),
    .grs(grs_r),
    .lsb(f2i_int_abs_r[0]),
    .roundup(roundup),
    .result_if_overflow(result_if_overflow)
  );

  ////////////////////////////////////////////////////
  //Registers
  always_ff @ (posedge clk) begin 
    if (advance) begin 
      done <= issue.new_request;
      done_r <= done;
      id <= issue.id;
      id_r <= id;
      rm[1] <= rm[0];
      rm[2] <= rm[1];

      rs1_hidden_bit[1] = rs1_hidden_bit[0];
      rs1_sign[1] <= rs1_sign[0];
      rs1_sign[2] <= rs1_sign[1];
      rs1_expo[1] <= rs1_expo[0];
      rs1_frac[1] <= rs1_frac[0]; 
      rs1_inf[1] <= rs1_inf[0];
      rs1_NaN[1] <= rs1_NaN[0];
      is_signed_r <= is_signed;
      result_sign_r <= result_sign;
      grs_r <= grs;
      f2i_int_abs_r <= f2i_int_abs;

      invalid_operationFlg <= invalid_operationExp; 
      invalid_operationFlg_r <= invalid_operationExp; 

      larger_than_unsigned_max_r <= larger_than_unsigned_max;
      larger_than_signed_max_r <= larger_than_signed_max; 
      smaller_than_unsigned_min_r <= smaller_than_unsigned_min;
      smaller_than_signed_min_r <= smaller_than_signed_min;

      rs1_expo_unbiased_r <= rs1_expo_unbiased;
      overflow_r <= overflow;
    end
  end

  ////////////////////////////////////////////////////
  //Output
  assign wb.rd = result_sign_r ? -(f2i_int_abs_r + XLEN'(roundup)) : (f2i_int_abs_r + XLEN'(roundup));
  assign wb.id = id_r;
  assign wb.done = done_r;
  assign wb.fflags = {invalid_operationFlg_r, 4'b0};
endmodule
