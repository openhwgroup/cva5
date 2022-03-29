import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module fp_sqrt (
  input logic clk,
  input logic rst,
  unit_issue_interface.unit issue,
  input fp_div_sqrt_inputs_t fp_div_sqrt_inputs,
  fp_unit_writeback_interface.unit wb
);
  typedef struct packed{
    id_t id;
  } sqrt_attributes_t;

  typedef struct packed{
    logic [FLEN-1:0] radicand;
    sqrt_attributes_t attr;
    logic hidden_bit;
    logic [3:0] special_case;
  } sqrt_fifo_inputs_t;
  parameter ITERATION = FRAC_WIDTH+1+3;
  parameter REMAINDER_BITS = FRAC_WIDTH+1-ITERATION;

  ////////////////////////////////////////////////////
  //Special Case and Exception Handling
  logic [3:0] special_case;
  logic is_inf, is_SNaN, is_zero, is_QNaN, is_denormal;
  logic invalid_operation;
  logic output_QNaN;
  logic output_zero;
  logic output_inf;
  logic output_one;
  logic early_terminate;
  logic [FLEN-1:0] early_terminate_result;
  logic [2:0] rm;

  //fp_special_case_detection_mp #(.FRAC_W(FRAC_WIDTH), .EXPO_W(EXPO_WIDTH)) 
    //special_case (
      //.input1(rs1),//fp_div_sqrt_inputs.rs1),
      //.is_inf(is_inf),
      //.is_SNaN(is_SNaN),
      //.is_QNaN(is_QNaN),
      //.is_zero(is_zero)
    //);
  assign {is_inf, is_SNaN, is_QNaN, is_zero} = sqrt_op.special_case;
  assign is_denormal = ~hidden_bit;// ~|rs1_expo;
  assign invalid_operation = rs1_sign & ~is_zero;
  assign output_inf = is_inf & ~rs1_sign;
  assign output_QNaN = is_SNaN | is_QNaN | invalid_operation;
  assign output_zero = is_zero | is_denormal;
  assign output_one = rs1_expo == {1'b0, {(EXPO_WIDTH-1){1'b1}}} & ~|rs1[0+:FRAC_WIDTH] & ~rs1_sign;
  assign early_terminate = output_inf | output_zero | output_QNaN | output_one;

  always_comb begin
    if (output_QNaN)
      early_terminate_result = CANONICAL_NAN;
    else if (output_inf)
      early_terminate_result = {1'b0, {EXPO_WIDTH{1'b1}}, FRAC_WIDTH'(0)};
    else if (output_zero)
      early_terminate_result = {fp_div_sqrt_inputs.rs1[FLEN-1], (FRAC_WIDTH+EXPO_WIDTH)'(0)};
    else 
      early_terminate_result = {2'b0, {(EXPO_WIDTH-1){1'b1}}, FRAC_WIDTH'(0)};
  end

  //Input FIFO
  sqrt_fifo_inputs_t fifo_inputs;
  assign fifo_inputs.radicand = fp_div_sqrt_inputs.rs1;
  assign fifo_inputs.attr.id = issue.id;
  assign fifo_inputs.hidden_bit = fp_div_sqrt_inputs.rs1_hidden_bit;
  assign fifo_inputs.special_case = fp_div_sqrt_inputs.rs1_special_case;

  fifo_interface #(.DATA_WIDTH($bits(sqrt_fifo_inputs_t))) input_fifo();
  taiga_fifo #(.DATA_WIDTH($bits(sqrt_fifo_inputs_t)), .FIFO_DEPTH(1)) 
    sqrt_input_fifo (
      .clk (clk),
      .rst (rst),
      .fifo (input_fifo)
    );

  sqrt_fifo_inputs_t sqrt_op;
  assign input_fifo.data_in = fifo_inputs;
  assign input_fifo.push = issue.new_request;
  assign input_fifo.potential_push = issue.new_request;
  assign input_fifo.pop = input_fifo.valid & ~in_progress;
  assign issue.ready = ~input_fifo.full | input_fifo.pop;
  assign sqrt_op = input_fifo.data_out;

  //If more than one cycle, set in_progress so that multiple div.start signals are not sent to the div unit.
  logic in_progress;
  set_clr_reg_with_rst #(.SET_OVER_CLR(1), .WIDTH(1), .RST_VALUE('0)) in_progress_m (
    .clk, .rst,
    .set(input_fifo.valid & (~in_progress)),
    .clr(wb.ack),
    .result(in_progress)
  );

  sqrt_attributes_t in_progress_attr;
  always_ff @ (posedge clk) begin
    if (input_fifo.pop)
      in_progress_attr <= sqrt_op.attr;
    if (issue.new_request)
      rm <= fp_div_sqrt_inputs.rm;
  end
  ////////////////////////////////////////////////////
  //sqrt mantissa core
  logic [FLEN-1:0] rs1;
  logic [FRAC_WIDTH:0] rs1_frac;
  logic [FRAC_WIDTH+3:0] sqrt_mantissa_input_odd_expo, sqrt_mantissa_input_even_expo, frac_sqrt;
  logic [FRAC_WIDTH:0] result_frac[1:0];
  logic [2:0] grs[1:0];
  logic [FLEN-1:0] result_if_overflow;
  logic roundup;
  unsigned_sqrt_interface #(.DATA_WIDTH(FRAC_WIDTH+4)) sqrt(); //DATA_WIDTH has to be power of 2

  assign rs1 = sqrt_op.radicand;
  assign rs1_frac = {sqrt_op.hidden_bit, rs1[0+:FRAC_WIDTH]};
  assign sqrt_mantissa_input_odd_expo = {4'b00, rs1_frac[FRAC_WIDTH:1]};
  assign sqrt_mantissa_input_even_expo = {3'b0, rs1_frac};
  assign sqrt.radicand = odd_exponent ? sqrt_mantissa_input_odd_expo : sqrt_mantissa_input_even_expo; 
  assign sqrt.start = input_fifo.pop;// & ~early_terminate;//input_fifo.valid & (~in_progress);
  assign sqrt.early_terminate = early_terminate;

  sqrt_mantissa #(.ITERATION(ITERATION)) sqrt_block (
    .clk (clk),
    .rst (rst),
    .sqrt (sqrt)
  );
  
  assign frac_sqrt = sqrt.quotient;
  assign {result_frac[0], grs[0]} = frac_sqrt;//sqrt.quotient;
  fp_round_simplified rounding (
    .sign (rs1_sign),
    .rm (rm),
    .grs (grs[0]),
    .lsb (result_frac[0][0]),
    .roundup (roundup),
    .result_if_overflow (result_if_overflow)
  );

  ////////////////////////////////////////////////////
  //Sign and Exponent handling
  logic rs1_sign;
  logic odd_exponent;
  logic [EXPO_WIDTH-1:0] rs1_expo;
  logic                  hidden_bit;
  logic [EXPO_WIDTH-1:0] unbiased_expo;
  logic [EXPO_WIDTH-1:0] unbiased_expo_abs;
  logic [EXPO_WIDTH-1:0] unbiased_result_expo;
  logic [EXPO_WIDTH-1:0] unbiased_result_expo_abs;
  logic [EXPO_WIDTH-1:0] result_expo;

  assign rs1_sign = rs1[FLEN-1];
  assign hidden_bit = sqrt_op.hidden_bit;
  assign rs1_expo = rs1[FLEN-2-:EXPO_WIDTH];
  assign unbiased_expo = rs1_expo - BIAS;
  assign odd_exponent = unbiased_expo[0];
  assign unbiased_expo_abs = unbiased_expo[EXPO_WIDTH-1] ? -unbiased_expo : unbiased_expo;
  assign unbiased_result_expo_abs = unbiased_expo_abs >> 1;
  assign unbiased_result_expo = unbiased_expo[EXPO_WIDTH-1] ? -unbiased_result_expo_abs : unbiased_result_expo_abs;
  assign result_expo = unbiased_result_expo + BIAS;

  ////////////////////////////////////////////////////
  assign wb.done = done_r;// | sqrt.done;
  assign wb.id = in_progress_attr.id;
  assign wb.grs = grs[0];
  assign wb.fflags = {invalid_operation, 3'b000, |grs[0]};
  assign wb.rm = rm;
  assign wb.carry = 0;
  assign wb.safe = 0;
  assign wb.hidden = result_frac[0][FRAC_WIDTH];
  assign wb.rd = early_terminate ? early_terminate_result : {rs1_sign, result_expo, result_frac[0][0+:FRAC_WIDTH]};
  //always_comb begin
    //if (early_terminate)
      //wb.rd = early_terminate_result;
    //else
      //wb.rd = {rs1_sign, result_expo, result_frac[0][0+:FRAC_WIDTH]};
  //end

  ////////////////////////////////////////////////////
  //Output
  logic done_r;
  always_ff @ (posedge clk) begin
    if (wb.ack)
      done_r <= 0;
    else if (sqrt.done)// | (early_terminate & input_fifo.pop))
      done_r <= 1;
  end
  ////////////////////////////////////////////////////
  //Register
  always_ff @ (posedge clk) begin
    result_frac[1] <= result_frac[0];
    grs[1] <= grs[0];
  end
endmodule

