import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module fp_normalize (
	//input logic [2:0] rm,
	input logic sign,
	input logic [EXPO_WIDTH-1:0] expo, 
	input logic [FRAC_WIDTH-1:0] frac,
    input fp_shift_amt_t left_shift_amt,
	input logic hidden_bit,
	input logic frac_safe_bit,	//preserved potential carry bit from mantissa addition/multiplication
    input logic frac_carry_bit,
	input grs_t grs_in, 
	output logic sign_norm,
	output logic [EXPO_WIDTH-1:0] expo_norm,
	output logic [FRAC_WIDTH-1:0] frac_norm,
	output logic hidden_bit_norm,
	//output logic frac_safe_bit_norm,
	output grs_t grs_norm,
	output logic overflow_before_rounding
	);
	
  	//clz includes the frac safe bit
	logic [EXPO_WIDTH-1:0] clz, clz_with_prepended_0s;
  	int i;
	logic frac_safe_bit_norm; 
    logic frac_carry_bit_norm;
	logic [FRAC_WIDTH+2:0] result_frac = {frac_carry_bit, frac_safe_bit, hidden_bit, frac};
	logic [FRAC_WIDTH+3:0] safe_hidden_frac_intermediate_g;
    logic [FRAC_WIDTH+$bits(grs_t)+2:0] safe_hidden_frac_intermediate_grs;
	grs_t grs;
	logic [$bits(grs_t):0] grs_buffer;
    logic [EXPO_WIDTH-1:0] expo_norm_right_shift, expo_norm_left_shift_intermediate, expo_norm_left_shift, expo_norm_underflow, right_shift_amt;//, left_shift_amt;
    logic [FRAC_WIDTH-1:0] frac_norm_right_shift, frac_norm_left_shift;
    logic frac_safe_bit_norm_right_shift, frac_safe_bit_norm_left_shift;
    logic frac_carry_bit_norm_right_shift, frac_carry_bit_norm_left_shift;
    logic hidden_bit_norm_right_shift, hidden_bit_norm_left_shift;
    logic underflow;
    grs_t grs_norm_right_shift, grs_norm_left_shift;

    //generate if (FRAC_WIDTH+2 <= 32) begin
      //clz frac_clz (
        //.clz_input (32'(result_frac)),
        //.clz (clz_with_prepended_0s[4:0])
      //);
      //assign clz = clz_with_prepended_0s - (32 - (FRAC_WIDTH + 3));
      //assign left_shift_amt = clz_with_prepended_0s - (32 - (FRAC_WIDTH + 1));
    //end else begin
      //clz_tree frac_clz (
        //.clz_input (64'(result_frac)),
        //.clz (clz_with_prepended_0s[5:0])
      //);
      //assign clz = clz_with_prepended_0s - (64 - (FRAC_WIDTH + 3));
      //assign left_shift_amt = clz_with_prepended_0s - (64 - (FRAC_WIDTH + 1));
    //end endgenerate
	
	assign sign_norm = sign;
	assign safe_hidden_frac_intermediate_g = {1'b0, frac_safe_bit, hidden_bit, frac, grs[$bits(grs_t)-1]};
    assign safe_hidden_frac_intermediate_grs = {1'b0, frac_safe_bit, hidden_bit, frac, grs};
	assign grs = grs_in;//rm == 1? '0 : grs_in;
	assign grs_buffer = {grs_in, 1'b0};

    always_comb begin
      //max right shift by 2
      right_shift_amt = 0;
      right_shift_amt[1:0] = {frac_carry_bit, ~frac_carry_bit & frac_safe_bit};
    end
    assign expo_norm_right_shift = expo + EXPO_WIDTH'(right_shift_amt);
    assign {frac_carry_bit_norm_right_shift, frac_safe_bit_norm_right_shift, hidden_bit_norm_right_shift, frac_norm_right_shift, grs_norm_right_shift} = {frac_carry_bit, frac_safe_bit, hidden_bit, frac, grs} >> right_shift_amt;
    //assign overflow_before_rounding = expo_norm > E_MAX | &expo; //overflow if expo exceeds 
    
    //assign left_shift_amt = clz ;//- 2;
    assign {underflow, expo_norm_left_shift_intermediate} = {1'b0, expo}  - {1'b0, left_shift_amt};
    assign expo_norm_left_shift = (expo_norm_left_shift_intermediate) & {EXPO_WIDTH{~underflow}}; //use underflow to mask expo = '0;
    assign expo_norm_underflow = '0;
    assign {frac_carry_bit_norm_left_shift, frac_safe_bit_norm_left_shift, hidden_bit_norm_left_shift, frac_norm_left_shift, grs_norm_left_shift} = {frac_carry_bit, frac_safe_bit, hidden_bit, frac, grs} << left_shift_amt;

    always_comb begin
      if (frac_carry_bit | frac_safe_bit) begin 
        expo_norm = expo_norm_right_shift;
        {frac_carry_bit_norm, frac_safe_bit_norm, hidden_bit_norm, frac_norm, grs_norm} = {frac_carry_bit_norm_right_shift, frac_safe_bit_norm_right_shift, hidden_bit_norm_right_shift, frac_norm_right_shift, grs_norm_right_shift};
      end else begin
        expo_norm = expo_norm_left_shift;
        {frac_carry_bit_norm, frac_safe_bit_norm, hidden_bit_norm, frac_norm, grs_norm} = {frac_carry_bit_norm_left_shift, frac_safe_bit_norm_left_shift, hidden_bit_norm_left_shift, frac_norm_left_shift, grs_norm_left_shift};
      end
    end
    //assertion sigs
    //logic safe_bit_norm_assert, hidden_assert;
    //logic [FRAC_WIDTH-1:0] frac_assert;
	//logic [2:0] grs_assert;
    //logic [EXPO_WIDTH-1:0] expo_norm_assert;
    //logic NaN, is_zero, is_subnormal, is_inf;
    //assign NaN = (expo == '1) && (frac != '0);
    //assign is_subnormal = (expo == '0);
    ////assign hidden_bit = ~is_subnormal;
    //assign is_zero = is_subnormal && (frac[FRAC_WIDTH-1:0] == '0);
    //assign is_inf = (expo == '1) && (frac[FRAC_WIDTH-1:0] == '0);


    ////implementation
    //always_comb begin
        //if (frac_safe_bit == 1) begin
            //{safe_bit_norm_assert, hidden_assert, frac_assert, grs_assert} = {frac_safe_bit, hidden_bit, frac, grs} >> 1;
            //expo_norm_assert = expo + 32'(1);
        //end else if (frac_safe_bit == 0 && hidden_bit == 1) begin
            //{safe_bit_norm_assert, hidden_assert, frac_assert, grs_assert} = {frac_safe_bit, hidden_bit, frac, grs};		
            //expo_norm_assert = expo;
        //end else begin 
            //for (i=0; i < FRAC_WIDTH; i++) begin	
                //if (32'(lshift_amt == i) || 32'(expo) <= i)
                    //break; 
            //end
            //expo_norm_assert = expo - i[EXPO_WIDTH-1:0];
            //{safe_bit_norm_assert, hidden_assert, frac_assert, grs_assert} = {frac_safe_bit, hidden_bit, frac, grs} << i[EXPO_WIDTH-1:0]; 
        //end 
    //end

	////assertions
    //result_frac_norm: assert property (
        //(!NaN && !is_subnormal && !is_zero && !is_inf)  |-> frac_norm == frac_assert);

    //result_expor_norm: assert property (
        //(!NaN && !is_subnormal && !is_zero && !is_inf) |-> expo_norm == expo_norm_assert);

    //result_hidden_norm: assert property (
        //(!NaN && !is_subnormal && !is_zero && !is_inf) |-> hidden_bit_norm == hidden_assert);

    //result_safebit_norm: assert property (
        //(!NaN && !is_subnormal && !is_zero && !is_inf) |-> frac_safe_bit_norm == 0);


endmodule : fp_normalize
