import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module fp_normalize (
	//input logic [2:0] rm,
	input logic sign,
	input logic [EXPO_WIDTH-1:0] expo, 
    input logic expo_overflow,
	input logic [FRAC_WIDTH-1:0] frac,
    input fp_shift_amt_t left_shift_amt,
    input subnormal,
    input right_shift,
    input logic [EXPO_WIDTH-1:0] right_shift_amt,
	input logic hidden_bit,
	input logic frac_safe_bit,	//preserved potential carry bit from mantissa addition/multiplication
    input logic frac_carry_bit,
	input grs_t grs_in, 
	output logic sign_norm,
	output logic [EXPO_WIDTH-1:0] expo_norm,
    output logic expo_overflow_norm,
	output logic [FRAC_WIDTH-1:0] frac_norm,
	output logic hidden_bit_norm,
	//output logic frac_safe_bit_norm,
	output grs_t grs_norm,
	output logic overflow_before_rounding
	);
	
  	//clz includes the frac safe bit
	logic [EXPO_WIDTH-1:0] clz, clz_with_prepended_0s;
	logic frac_safe_bit_norm; 
    logic frac_carry_bit_norm;
	grs_t grs;
    logic [EXPO_WIDTH:0] expo_norm_right_shift, expo_norm_left_shift;// right_shift_amt;
    logic [FRAC_WIDTH-1:0] frac_norm_right_shift, frac_norm_left_shift;
    logic frac_safe_bit_norm_right_shift, frac_safe_bit_norm_left_shift;
    logic frac_carry_bit_norm_right_shift, frac_carry_bit_norm_left_shift;
    logic hidden_bit_norm_right_shift, hidden_bit_norm_left_shift;
    grs_t grs_norm_right_shift, grs_norm_left_shift;
    logic [EXPO_WIDTH:0] subnormal_expo, subnormal_right_shift_amt;

    logic [EXPO_WIDTH:0] normal_expo; 
    logic [1:0] normal_right_shift_amt;

    logic expo_less_than_left_shift_amt;
    fp_shift_amt_t left_shift_amt_adjusted;
    logic [EXPO_WIDTH-1:0] expo_norm_left_shift_intermediate;

    ////////////////////////////////////////////////////
    //Implementation
    //Expo_overflow: FMUL, FDIV can assert
    //Expo_overflow_norm: FADD, FMUL can assert due to right shifting
    assign sign_norm = sign;
    assign grs = grs_in;//rm == 1? '0 : grs_in;

    //Righ Shift
    //Needed by: FADD, FDIV, FMUL
    //The right shift amt is calculated by each unit; subnormal needs to support larger right shifter due to the multiplication's pre-normalization; normal's right shift amt cannot exceed 2
    generate if (ENABLE_SUBNORMAL) begin
      assign subnormal_expo = {expo_overflow, expo} & {(EXPO_WIDTH+1){~subnormal}};
      assign subnormal_right_shift_amt = (EXPO_WIDTH+1)'(right_shift_amt) & {(EXPO_WIDTH+1){~subnormal}};
      assign expo_norm_right_shift = subnormal_expo + subnormal_right_shift_amt;
      assign {frac_carry_bit_norm_right_shift, frac_safe_bit_norm_right_shift, hidden_bit_norm_right_shift, frac_norm_right_shift, grs_norm_right_shift} = {frac_carry_bit, frac_safe_bit, hidden_bit, frac, grs} >> right_shift_amt;
    end else begin
      assign normal_expo = {expo_overflow, expo};
      assign normal_right_shift_amt = right_shift_amt[1:0];
      assign expo_norm_right_shift = normal_expo + (EXPO_WIDTH+1)'(normal_right_shift_amt);
      assign {frac_carry_bit_norm_right_shift, frac_safe_bit_norm_right_shift, hidden_bit_norm_right_shift, frac_norm_right_shift, grs_norm_right_shift} = {frac_carry_bit, frac_safe_bit, hidden_bit, frac, grs} >> normal_right_shift_amt;
    end endgenerate

    //Left Shift
    //Neededby: FSUB; FSQRT if subnormal is enabled
    //Left shift is done by first reversing the bit order and sign-shited(>>>)
    //This is needed to preserve the sticky bit
    logic signed [FRAC_WIDTH+3+3-1:0] left, reversed_left, reversed_left_shifted, left_shifted;
    assign left = {frac_carry_bit, frac_safe_bit, hidden_bit, frac, grs};
    genvar i;
    generate 
      for (i = 0; i < (FRAC_WIDTH+3+3); i++) begin
        assign reversed_left[i] = left[FRAC_WIDTH+3+3-1-i];
      end
    endgenerate
    assign reversed_left_shifted = reversed_left >>> left_shift_amt_adjusted;
    generate 
      for (i = 0; i < (FRAC_WIDTH+3+3); i++) begin
        assign left_shifted[i] = reversed_left_shifted[FRAC_WIDTH+3+3-1-i];
      end
    endgenerate

    always_comb begin
      {expo_less_than_left_shift_amt, expo_norm_left_shift_intermediate} = expo - (EXPO_WIDTH)'(left_shift_amt);
      left_shift_amt_adjusted = expo_less_than_left_shift_amt ? expo : left_shift_amt;
      {frac_carry_bit_norm_left_shift, frac_safe_bit_norm_left_shift, hidden_bit_norm_left_shift, frac_norm_left_shift, grs_norm_left_shift} = left_shifted;
    end
    generate if (ENABLE_SUBNORMAL) 
      //FADD of two subnormals may result in promotion of subnormal to normal
      //This is handled by adding 1 to the expo if the hidden_bit is 1, and |expo==0
      assign expo_norm_left_shift = ({expo_norm_left_shift_intermediate & {(EXPO_WIDTH){~expo_less_than_left_shift_amt}}}) + (EXPO_WIDTH)'({subnormal&hidden_bit}); 
    else 
      assign expo_norm_left_shift = {1'b0, expo_norm_left_shift_intermediate & {(EXPO_WIDTH){~expo_less_than_left_shift_amt}}}; //drive exponent to 0s if left shift amt > expo
    endgenerate

    //Output Selection
    always_comb begin
        if (right_shift) begin 
          {expo_overflow_norm, expo_norm} = expo_norm_right_shift;
          {frac_carry_bit_norm, frac_safe_bit_norm, hidden_bit_norm, frac_norm, grs_norm} = {frac_carry_bit_norm_right_shift, frac_safe_bit_norm_right_shift, hidden_bit_norm_right_shift, frac_norm_right_shift, grs_norm_right_shift};
        end else begin
          {expo_overflow_norm, expo_norm} = expo_norm_left_shift;
          {frac_carry_bit_norm, frac_safe_bit_norm, hidden_bit_norm, frac_norm, grs_norm} = {frac_carry_bit_norm_left_shift, frac_safe_bit_norm_left_shift, hidden_bit_norm_left_shift, frac_norm_left_shift, grs_norm_left_shift};
        end
      overflow_before_rounding = expo_overflow_norm | (&expo_norm);
      end
endmodule : fp_normalize
