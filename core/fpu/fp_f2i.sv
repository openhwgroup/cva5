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

  id_t                        id, r_id;
  logic                       done, r_done;
  localparam                  NUM_STICKY_LUTS = (FRAC_WIDTH+1-2-1)/6+1; //number of 6-input LUTs
  localparam                  NUM_INT_LUTS = (XLEN-1)/6+1;
  logic                       sign;
  logic [EXPO_WIDTH-1:0]      expo_unbiased;
  logic [FRAC_WIDTH:0]        rs1_frac;
  logic [XLEN+FRAC_WIDTH-1:0]   shift_in;
  logic [XLEN+FRAC_WIDTH-1:0]   f2i_int_dot_frac;
  logic                       f2i_int_less_than_1;
  logic [EXPO_WIDTH-1:0]      abs_expo_unbiased;
  logic                       expo_unbiased_greater_than_31;
  logic                       expo_unbiased_greater_than_30;
  logic                       is_signed, r_is_signed;
  logic [2:0]                 rm;

  logic [XLEN-1:0]            f2i_int, r_f2i_int;
  logic [FRAC_WIDTH:0]        f2i_frac;
  logic [2:0]                 grs;
  logic                       sticky;
  logic                       inexact, r_inexact;
  logic [NUM_STICKY_LUTS-1:0] f2i_frac_sticky_OR;
  logic                       roundup;
  logic [FLEN-1:0]            result_if_overflow;

  logic [NUM_INT_LUTS-1:0]    largest_unsigned_int_AND;//check if f2i_int == FFFFFFFF
  logic [NUM_INT_LUTS-1:0]    largest_signed_int_AND;  //check if f2i_int == 7fffffff
  logic [NUM_INT_LUTS-1:0]    smallest_signed_int_OR; //check if f2i_int == 80000000
  logic                       largest_unsigned_int;
  logic                       largest_signed_int;
  logic                       smallest_signed_int;
  logic                       greater_than_largest_unsigned_int, r_greater_than_largest_unsigned_int;
  logic                       greater_than_largest_signed_int, r_greater_than_largest_signed_int;
  logic                       smaller_than_smallest_signed_int, r_smaller_than_smallest_signed_int;
  logic [XLEN-1:0]            special_case_result, r_special_case_result;
  logic                       special, r_special;

  logic                       subtract, r_subtract;
  logic [XLEN-1:0]            in1, in2, r_in1, r_in2;
  logic                       carry_in;
  logic [XLEN-1:0]            f2i_int_rounded;

  ////////////////////////////////////////////////////
  //Implementation
  //Cycle 1
  
  //input unpacking
  assign sign = fp_f2i_inputs.sign;
  assign expo_unbiased = fp_f2i_inputs.expo_unbiased;
  assign rs1_frac = fp_f2i_inputs.frac;
  assign shift_in = {{(XLEN-1){1'b0}}, rs1_frac};
  assign f2i_int_less_than_1 = fp_f2i_inputs.f2i_int_less_than_1;
  assign abs_expo_unbiased = fp_f2i_inputs.abs_expo_unbiased;
  assign expo_unbiased_greater_than_31 = fp_f2i_inputs.expo_unbiased_greater_than_31;
  assign expo_unbiased_greater_than_30 = fp_f2i_inputs.expo_unbiased_greater_than_30;
  assign is_signed = fp_f2i_inputs.is_signed;
  assign rm = fp_f2i_inputs.rm;

  //left shift
  assign f2i_int_dot_frac = shift_in << expo_unbiased;
  always_comb begin
    if (f2i_int_less_than_1) begin
      f2i_int = 0;
      f2i_frac = rs1_frac;
    end else begin
      {f2i_int, f2i_frac} = {f2i_int_dot_frac, 1'b0};
    end
  end

  //calculate rounding bit and -roundup or +roundup 
  parallel_OR #(.WIDTH(NUM_STICKY_LUTS)) f2i_frac_sticky(
    .i_data((NUM_STICKY_LUTS*6)'(f2i_frac[FRAC_WIDTH-2:0])),
    .o_data(f2i_frac_sticky_OR)
  );

  assign sticky = |f2i_frac_sticky_OR;
  always_comb begin
    if (f2i_int_less_than_1) begin
      if (abs_expo_unbiased == 1) 
        grs = { f2i_frac[FRAC_WIDTH-:2], sticky };
      else if (abs_expo_unbiased == 2)
        grs = { 1'b0, f2i_frac[FRAC_WIDTH], f2i_frac[FRAC_WIDTH-1] | sticky };
      else
        grs = { 2'b0, (|f2i_frac[FRAC_WIDTH-:2] | sticky) };
    end else begin
        grs = { f2i_frac[FRAC_WIDTH-:2], sticky };
    end
  end

  fp_round_simplified f2i_int_roundup (
    .sign(sign),
    .rm(rm),
    .grs(grs),
    .lsb(f2i_int[0]),
    .roundup(roundup),
    .result_if_overflow(result_if_overflow)
  );

  assign subtract = fp_f2i_inputs.subtract;
  assign in1 = subtract ? -(XLEN'(roundup)) : XLEN'(roundup); 
 
  //Special case handling
  parallel_AND #(.WIDTH(NUM_INT_LUTS)) largest_signed_int_AND_inst(
    .i_data( {{(NUM_INT_LUTS*6-XLEN+1){1'b1}}, f2i_int[XLEN-2:0]} ),
    .o_data(largest_signed_int_AND)
  );

  parallel_OR #(.WIDTH(NUM_INT_LUTS)) smallest_unsigned_int_AND_inst(
    .i_data((NUM_INT_LUTS*6)'(f2i_int[XLEN-2:0])),
    .o_data(smallest_signed_int_OR)
  );

  assign inexact = |grs;
  assign greater_than_largest_unsigned_int = (~is_signed) & ((f2i_int[XLEN-1] & largest_unsigned_int & inexact) | expo_unbiased_greater_than_31);
  assign greater_than_largest_signed_int   = (is_signed & ~sign) & ((~f2i_int[XLEN-1] & largest_signed_int & |grs) | expo_unbiased_greater_than_30);
  assign smaller_than_smallest_signed_int  = (is_signed & sign) & ((f2i_int[XLEN-1] & (~|smallest_signed_int_OR | inexact)) | expo_unbiased_greater_than_31);
  assign special = (~is_signed & (greater_than_largest_unsigned_int | sign)) | 
                   (is_signed & (greater_than_largest_signed_int | smaller_than_smallest_signed_int));
  
  always_comb begin
    if (r_greater_than_largest_unsigned_int) 
      special_case_result = 32'hffffffff;//2^32 - 1;
    else if (r_greater_than_largest_signed_int)
      special_case_result = 32'h7fffffff;//2^31 - 1;
    else if (r_smaller_than_smallest_signed_int) 
      special_case_result = 32'h80000000;//-2^31;
    else
      special_case_result = 0;
  end

  ////////////////////////////////////////////////////
  //Cycle 2
  //calculate signed f2i_int
  //Input negative: f2i_int_rouned = -roundup - f2i_int 
  //Input positive: f2i_int_rouned =  roundup + f2i_int 
  assign in2 = r_f2i_int ^ {XLEN{r_subtract}};
  assign {f2i_int_rounded, carry_in} = {r_in1, 1'b1} + {in2, r_subtract};

  //Registers
  always_ff @ (posedge clk) begin
    if (advance) begin
      id <= issue.id;
      done <= issue.new_request;

      r_greater_than_largest_unsigned_int <= greater_than_largest_unsigned_int;
      r_greater_than_largest_signed_int <= greater_than_largest_signed_int;
      r_smaller_than_smallest_signed_int <= smaller_than_smallest_signed_int;
      r_inexact <= inexact;

      r_is_signed <= is_signed;

      r_f2i_int <= f2i_int;
      r_in1 <= in1;
      r_subtract <= subtract;

      r_special_case_result <= special_case_result;
      r_special <= special;
    end
  end

  ////////////////////////////////////////////////////
  //Output
  assign wb.rd = r_special ? special_case_result : f2i_int_rounded;
  assign wb.id = id;
  assign wb.done = done;
  assign wb.fflags = {r_special, 3'b0, r_inexact & ~r_special};
endmodule
