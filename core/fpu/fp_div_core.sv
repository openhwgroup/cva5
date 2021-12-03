//TODO: calculate frac_width+2 bits of mantissa to satisfy correctly rounding
import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module fp_div_core (
  input logic                   clk,
  input logic                   rst,
  input fp_div_sqrt_inputs_t    fp_div_sqrt_inputs,
  input logic                   start_algorithm,
  fp_unit_writeback_interface.unit fp_wb
);

  unsigned_division_interface #(.DATA_WIDTH(2*FRAC_WIDTH+3)) div();
  logic                   start_algorithm_r;
  logic                   done[1:0];
  id_t                    id_in_progress;
  logic [FLEN-1:0]        rs1, rs2;
  logic                   rs1_hidden_bit, rs2_hidden_bit;
  logic                   rs1_sign, rs2_sign;
  logic [EXPO_WIDTH-1:0]  rs1_expo, rs2_expo;
  logic                   rs1_normal, rs2_normal;
  logic [FRAC_WIDTH:0]    rs1_frac, rs2_frac;
  logic [2:0]             rm;
  logic                   rs1_is_inf, rs1_is_SNaN, rs1_is_QNaN, rs1_is_zero;
  logic                   rs2_is_inf, rs2_is_SNaN, rs2_is_QNaN, rs2_is_zero;
  logic                   early_terminate, invalid_operation, output_QNaN, output_zero, output_inf, div_by_zero;
  logic                   result_sign[1:0];
  logic [EXPO_WIDTH:0]    result_expo;
  logic [EXPO_WIDTH-1:0]  result_expo_intermediate [1:0];
  logic                   result_hidden; //the integer part
  logic [FRAC_WIDTH-1:0]  result_frac;
  logic [2:0]             grs;
  logic [2:0]             rounding_grs[1:0];
  logic [FLEN+1:0]        result_norm[1:0];
  logic                   roundup;
  logic [FLEN-1:0]        result_if_overflow;
  logic                   result_sign_out;
  logic [EXPO_WIDTH-1:0]  result_expo_out;
  logic [FRAC_WIDTH-1:0]  result_frac_out;
  logic [FRAC_WIDTH+1:0]  result_frac_round;
  logic                   inexact, underflow, overflow;

  //Input pre-processing
  always_ff@(posedge clk) begin
    if (start_algorithm) begin
        rs1 <= fp_div_sqrt_inputs.rs1;
        rs2 <= fp_div_sqrt_inputs.rs2;
        rm <= fp_div_sqrt_inputs.rm;
        rs1_hidden_bit <= fp_div_sqrt_inputs.rs1_hidden_bit;
        rs2_hidden_bit <= fp_div_sqrt_inputs.rs2_hidden_bit;
        id_in_progress <= fp_div_sqrt_inputs.id;
        rs1_is_inf <= fp_div_sqrt_inputs.rs1_special_case[3];
        rs1_is_SNaN <= fp_div_sqrt_inputs.rs1_special_case[2];
        rs1_is_QNaN <= fp_div_sqrt_inputs.rs1_special_case[1];
        rs1_is_zero <= fp_div_sqrt_inputs.rs1_special_case[0];
        rs2_is_inf <= fp_div_sqrt_inputs.rs2_special_case[3];
        rs2_is_SNaN <= fp_div_sqrt_inputs.rs2_special_case[2];
        rs2_is_QNaN <= fp_div_sqrt_inputs.rs2_special_case[1];
        rs2_is_zero <= fp_div_sqrt_inputs.rs2_special_case[0];
    end
  end

  //unpack
  //assign rm          = fp_div_sqrt_inputs.rm;
  assign rs1_sign    = rs1[FLEN-1];
  assign rs2_sign    = rs2[FLEN-1];
  assign rs1_expo    = rs1[FLEN-2-:EXPO_WIDTH];
  assign rs2_expo    = rs2[FLEN-2-:EXPO_WIDTH];
  assign rs1_normal  = rs1_hidden_bit;//|rs1_expo;
  assign rs2_normal  = rs2_hidden_bit;//|rs2_expo;
  assign rs1_frac    = {rs1_normal, rs1[0+:FRAC_WIDTH]};
  assign rs2_frac    = {rs2_normal, rs2[0+:FRAC_WIDTH]};

  assign invalid_operation = (rs1_is_zero & rs2_is_zero) | (rs1_is_inf & rs2_is_inf) | rs1_is_SNaN | rs2_is_SNaN;
  assign div_by_zero       = ~rs1_is_zero & ~rs1_is_inf & (rs2_is_zero);// | ~rs2_normal);
  assign output_QNaN       = invalid_operation | rs1_is_QNaN | rs2_is_QNaN;
  assign output_inf        = ~output_QNaN & (div_by_zero | rs1_is_inf);// | overflow);
  assign output_zero       = ~output_QNaN & (rs1_is_zero | ~rs1_normal | rs2_is_inf);// | underflow);
  assign early_terminate   = output_QNaN | output_inf | output_zero;
  assign result_sign[0]    = rs1_sign ^ rs2_sign;
  assign result_expo_intermediate[0] = rs1_expo - rs2_expo;

  //mantissa division  
  assign div.dividend  = {rs1_frac, {(FRAC_WIDTH+2){1'b0}}};
  assign div.divisor   = {{(FRAC_WIDTH+2){1'b0}}, rs2_frac};
  assign div.start     = start_algorithm_r & ~early_terminate;     //start div if no special cases
  assign div.divisor_is_zero = rs2_is_zero;
  assign result_expo_intermediate[0] = rs1_expo - rs2_expo;
  //fp_div_quick_clz #(FRAC_WIDTH+2) div_mantissa (.*);  
  fp_div_radix2 #(.DIV_WIDTH(2*FRAC_WIDTH+3)) div_mantissa (.*);  

  assign result_expo   = result_expo_intermediate[1] + BIAS;// rs1_expo - rs2_expo + BIAS;
  assign result_hidden = div.quotient[FRAC_WIDTH+2];
  assign result_frac   = div.quotient[2+:FRAC_WIDTH];
  assign grs           = {div.quotient[1:0], |div.remainder[0+:FRAC_WIDTH+2]};

  grs_t                          grs_norm; 
  grs_t                          grs_round;
  logic                          result_sign_norm [1:0];
  logic                          overflow_before_rounding;
  logic [EXPO_WIDTH-1:0]         result_expo_norm [1:0];
  logic [FRAC_WIDTH:0]           result_frac_norm [1:0];

  // calculate CLZ 
  logic [EXPO_WIDTH-1:0] clz, clz_with_prepended_0s, left_shift_amt;
  generate if (FRAC_WIDTH+2 <= 32) begin
    clz frac_clz (
      .clz_input (32'({result_hidden, result_frac})),
      .clz (clz_with_prepended_0s[4:0])
    );
    assign left_shift_amt = clz_with_prepended_0s - (32 - (FRAC_WIDTH + 1));
  end else begin
    clz_tree frac_clz (
      .clz_input (64'({result_hidden, result_frac})),
      .clz (clz_with_prepended_0s[5:0])
    );
    assign left_shift_amt = clz_with_prepended_0s - (64 - (FRAC_WIDTH + 1));
  end endgenerate

  logic [FLEN-1:0] special_case_results[1:0];
  logic output_special_case[1:0];
  always_comb begin
    if(output_inf) begin
      special_case_results[0] = {result_sign[0], {(EXPO_WIDTH){1'b1}}, {(FRAC_WIDTH){1'b0}}}; 
      output_special_case[0] = 1;
    end else if (output_QNaN) begin 
      special_case_results[0] = CANONICAL_NAN;
      output_special_case[0] = 1;
    end else if (output_zero) begin
      special_case_results[0] = {result_sign[0], (FLEN-1)'(0)};
      output_special_case[0] = 1;
    end else begin
      //outputzero
      special_case_results[0] = {result_sign[0], (FLEN-1)'(0)};
      output_special_case[0] = 0;
    end
  end

  logic advance;
  assign advance = ~fp_wb.done | fp_wb.ack;
  assign fp_wb.done = done[0];
  assign fp_wb.id = id_in_progress;
  assign fp_wb.fflags = {1'b0, div_by_zero, 3'b0};// ,|grs_round & ~early_terminate};
  assign fp_wb.rm = rm;
  assign fp_wb.rd = output_special_case[0] ? special_case_results[0] : 
                                             {result_sign[0], result_expo[EXPO_WIDTH-1:0], result_frac[FRAC_WIDTH-1:0]};
  assign fp_wb.clz = left_shift_amt;
  assign fp_wb.hidden = result_hidden;
  assign fp_wb.safe = 1'b0;
  assign fp_wb.carry = 1'b0;
  assign fp_wb.grs = grs & {$bits(grs_t){~output_special_case[0]}};

  //Registers
  always_ff @ (posedge clk) begin 
    if (advance) begin 
      done[0] <= (early_terminate & start_algorithm_r) | div.done;
      //pipeline
      grs_round <= grs_norm;
      result_sign[1] <= result_sign[0];
      result_norm[1] <= result_norm[0];
      result_expo_intermediate[1] <= result_expo_intermediate[0];
      start_algorithm_r <= start_algorithm;
      result_sign_norm[1] <= result_sign_norm[0];
      result_expo_norm[1] <= result_expo_norm[0];
      result_frac_norm[1] <= result_frac_norm[0];    
    end
  end
endmodule : fp_div_core
