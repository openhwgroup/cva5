//potentially in the critical path
//can register inputs for better timing with worse latency (4)
import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

//TODO: rs1 coming from fmul with grs might be the input with smaller exponent,
//thus alignment needs to shift grs bits as well
module fp_add_madd_fused (
  input logic clk,
  input logic rst,
  input logic fma_mul_invalid_operation,
  input grs_t fp_add_grs,
  input logic swap,
  input logic [EXPO_WIDTH:0] expo_diff_in,
  input fp_add_inputs_t fp_add_inputs,
  unit_issue_interface.unit issue,
  //output fp_unit_writeback_t fp_wb
  fp_unit_writeback_interface.unit fp_wb
  //output logic [4:0] fflags
  );
  
  logic [FLEN-1:0]               rs1;
  logic [FLEN-1:0]               rs2;
  logic [FLEN-1:0]               temp_rs1;
  logic [FLEN-1:0]               temp_rs2;
  logic                          temp_rs1_sign[1:0];
  logic                          temp_rs2_sign[1:0];
  logic [EXPO_WIDTH-1:0]         temp_rs1_expo[1:0];
  logic [EXPO_WIDTH-1:0]         temp_rs2_expo[1:0];
  logic [FRAC_WIDTH-1:0]         temp_rs1_frac[1:0];
  logic [FRAC_WIDTH-1:0]         temp_rs2_frac[1:0];
  logic 			             temp_rs1_hidden[1:0], temp_rs2_hidden[1:0];
  logic                          temp_rs1_safe, temp_rs2_safe;
  grs_t                          fp_add_grs_r;
  logic [FLEN-1:0]               result;
  logic [2:0]                    rm [3:0];
  logic [6:0]                    fn7;
  logic                          add;

  logic                          rs1_sign [1:0];
  logic [EXPO_WIDTH-1:0]         rs1_expo [1:0];
  logic [FRAC_WIDTH+1:0]         rs1_frac [1:0];
  logic                          rs2_sign [1:0];
  logic [EXPO_WIDTH-1:0]         rs2_expo [1:0];
  logic [FRAC_WIDTH+1:0]         rs2_frac [1:0];
  logic                          rs1_safe_bit [1:0], rs2_safe_bit[1:0];

  logic [FRAC_WIDTH+GRS_WIDTH:0] rs1_frac_2s [1:0];
  logic [FRAC_WIDTH+GRS_WIDTH:0] rs2_frac_2s [1:0];  

  logic                          zero_result_sign[3:0];
  logic                          subtract[1:0];
  logic                          result_sign [2:0];
  logic [EXPO_WIDTH-1:0]         result_expo [1:0];
  logic [FRAC_WIDTH+2:0]         result_frac [1:0];
  logic                          result_sign_norm [2:0];
  logic [EXPO_WIDTH-1:0]         result_expo_norm [2:0];
  logic [FRAC_WIDTH:0]           result_frac_norm [2:0];

  logic [EXPO_WIDTH:0]           expo_diff[1:0], expo_diff_negate;
  logic [EXPO_WIDTH:0]           align_shift_amt;
  logic [FRAC_WIDTH+1:0]         rs2_frac_aligned[1:0];  
  grs_t                          grs_in;
  grs_t                          rs1_grs[1:0], rs2_grs[1:0];
  grs_t                          grs;//guard, round, sticky bits
  grs_t                          grs_norm;
  grs_t                          grs_round;
  logic                          overflow_before_rounding [2:0];
  logic                          roundup[1:0];
  logic [FLEN-1:0]               result_if_overflow[1:0];
  logic                          sign_round_out;
  logic [EXPO_WIDTH-1:0]         expo_round_out;
  logic [FRAC_WIDTH:0]           frac_round_out;
  logic                          safe_bit_round;
  (* use_dsp = "no" *) logic [FRAC_WIDTH+1:0]         frac_round_intermediate;
  logic                          inexact[3:0];
  logic                          underflowFlg, overflowFlg, inexactFlg;
  logic                          underflowExp, overflowExp, inexactExp;
  logic                          invalid_operation[4:0];
  logic				             output_QNaN[4:0];
  logic 			             output_inf[4:0];
  logic				             rs1_inf, rs2_inf;
  logic                          rs1_NaN, rs2_NaN;
  logic                          rs1_zero, rs2_zero;
  logic                          done [3:0];
  id_t                           id [3:0];
  //logic [CLZ_WIDTH-1:0]          clz; 

  ///////////////////////////////////
  //Implementation
  assign rm[0] = fp_add_inputs.rm;
  assign fn7 = fp_add_inputs.fn7;
  assign add = fn7 == FADD;
  assign temp_rs1 = fp_add_inputs.rs1;
  assign temp_rs2 = fp_add_inputs.rs2;
  assign temp_rs1_sign[0] = temp_rs1[FLEN-1];
  assign temp_rs2_sign[0] = add ? temp_rs2[FLEN-1] : ~temp_rs2[FLEN-1]; //replace mux with xor
  assign temp_rs1_expo[0] = temp_rs1[FLEN-2-:EXPO_WIDTH];
  assign temp_rs2_expo[0] = temp_rs2[FLEN-2-:EXPO_WIDTH];
  assign temp_rs1_frac[0] = temp_rs1[0+:FRAC_WIDTH];
  assign temp_rs2_frac[0] = temp_rs2[0+:FRAC_WIDTH];
  assign temp_rs1_safe = fp_add_inputs.rs1_safe_bit;
  assign temp_rs2_safe = fp_add_inputs.rs2_safe_bit;
  assign temp_rs1_hidden[0] = fp_add_inputs.rs1_hidden_bit;
  assign temp_rs2_hidden[0] = fp_add_inputs.rs2_hidden_bit;

  //invalid operation exception and special inputs handling
  //SNAN inputs or "magnitude subtraction of infinities" 
  assign rs1_inf = fp_add_inputs.rs1_special_case[3];
  assign rs2_inf = fp_add_inputs.rs2_special_case[3];
  assign rs1_NaN = |fp_add_inputs.rs1_special_case[2:1];
  assign rs2_NaN = |fp_add_inputs.rs2_special_case[2:1];

  assign invalid_operation[0] = fma_mul_invalid_operation || fp_add_inputs.rs1_special_case[2] || fp_add_inputs.rs2_special_case[2] ||
                                (rs1_inf & rs2_inf & (temp_rs1_sign[0] ^ temp_rs2_sign[0])); //substraction in magnitude of infinities
  assign inexact[0] = |fp_add_grs;
  assign output_QNaN[0] = rs1_NaN || rs2_NaN || invalid_operation[0];
  assign output_inf[0] = (rs1_inf || rs2_inf) && !output_QNaN[0];
  assign expo_diff[0] = expo_diff_in;//temp_rs1_expo[0] - temp_rs2_expo[0];
  assign expo_diff_negate = temp_rs2_expo[0] - temp_rs1_expo[0];
  assign zero_result_sign[0] = rm[0] == 3'b010 ? 1 : 0;
  assign subtract[0] = temp_rs1_sign[0] ^ temp_rs2_sign[0];

  //normal case
  //extract fields
  always_comb begin 
    //if(~expo_diff[0][EXPO_WIDTH]) begin //move input with larger expo to rs1
    if(~swap) begin //move input with larger expo to rs1
      rs1_sign[0] = temp_rs1_sign[0];
      rs1_expo[0] = temp_rs1_expo[0];
      rs1_safe_bit[0] = temp_rs1_safe;
      rs1_frac[0] = {temp_rs1_safe, temp_rs1_hidden[0], temp_rs1_frac[0]};
      rs1_grs[0] = fp_add_grs;
      
      rs2_sign[0] = temp_rs2_sign[0];
      rs2_expo[0] = temp_rs2_expo[0];
      rs2_frac[0] = {temp_rs2_safe,temp_rs2_hidden[0], temp_rs2_frac[0]}; 
      rs2_grs[0] = 'b0;
      rs2_safe_bit[0] = temp_rs2_safe;
    end else begin 
      rs1_sign[0] = temp_rs2_sign[0];
      rs1_expo[0] = temp_rs2_expo[0];
      rs1_frac[0] = {temp_rs2_safe,temp_rs2_hidden[0], temp_rs2_frac[0]};
      rs1_grs[0] = 'b0;
      rs1_safe_bit[0] = temp_rs2_safe;

      rs2_sign[0] = temp_rs1_sign[0];
      rs2_expo[0] = temp_rs1_expo[0];
      rs2_frac[0] = {temp_rs1_safe,temp_rs1_hidden[0], temp_rs1_frac[0]}; 
      rs2_grs[0] = fp_add_grs;
      rs2_safe_bit[0] = temp_rs1_safe;
    end
  end

  //alignment and rounding bits calculation
  logic rs2_frac_sticky_bit;
  logic rs2_grs_sticky_bit[1:0]; // this can come from FMA.FMUL from which rounding has not been performed
  logic expo_diff_larger_than_frac_width[1:0];
  localparam SHIFT_AMT_WIDTH = $clog2(FRAC_WIDTH+1);
  logic [SHIFT_AMT_WIDTH-1:0] shft_amt;

  assign align_shift_amt = expo_diff[0];
  assign expo_diff_larger_than_frac_width[0] = |align_shift_amt[EXPO_WIDTH-1:SHIFT_AMT_WIDTH];
  assign shft_amt = align_shift_amt[SHIFT_AMT_WIDTH-1:0];
  assign {rs2_frac_aligned[0], grs_in[2:1]} = {rs2_frac[0], rs2_grs[0][GRS_WIDTH-1-:2]} >> align_shift_amt;
  assign rs2_grs_sticky_bit[0] = rs2_grs[0][0];
  assign grs_in[0] = rs2_frac_sticky_bit;

  sticky_bit_logic # (.INPUT_WIDTH(FRAC_WIDTH+2)) frac_sticky (
    .shifter_input (rs2_frac[0]),
    .shift_amount (shft_amt),
    .sticky_bit (rs2_frac_sticky_bit)
  );

  //perform addition
  //always_comb begin 
    //if(~expo_diff[1][EXPO_WIDTH]) begin //move input with larger expo to rs1
      //rs1_sign[1] = temp_rs1_sign[1];
      //rs1_expo[1] = temp_rs1_expo[1];
      //rs1_frac[1] = {temp_rs1_hidden[1], temp_rs1_frac[1]};
      //rs1_grs[1] = fp_add_grs_r;
    //end else begin 
      //rs1_sign[1] = temp_rs2_sign[1];
      //rs1_expo[1] = temp_rs2_expo[1];
      //rs1_frac[1] = {temp_rs2_hidden[1], temp_rs2_frac[1]};
      //rs1_grs[1] = 'b0;
   //end
  //end

  logic [FRAC_WIDTH+GRS_WIDTH+2:0] adder_in1, adder_in2, adder_in1_1s, adder_in2_1s;
  logic [FRAC_WIDTH+GRS_WIDTH+3:0] in1, in2;
  (* use_dsp = "no" *) logic [FRAC_WIDTH+2:0] result_frac_intermediate;
  (* use_dsp = "no" *) grs_t                          grs_intermediate;
  (* use_dsp = "no" *) logic adder_carry_out;
  (* use_dsp = "no" *) logic add_sub_carry_in;
  (* use_dsp = "no" *) grs_t                          grs_add;
  logic output_zero;

  //LUT adder
  assign adder_in1 = {1'b0, rs1_frac[1], rs1_grs[1]};
  assign adder_in2 = {1'b0, rs2_frac_aligned[1] & {(FRAC_WIDTH+2){~expo_diff_larger_than_frac_width[1]}}, {rs2_grs[1][2:1], rs2_grs[1][0] | rs2_grs_sticky_bit[1]}};
  assign adder_in1_1s = adder_in1;
  assign adder_in2_1s = adder_in2 ^ {(FRAC_WIDTH+GRS_WIDTH+3){subtract[1]}};
  assign in1 = {adder_in1_1s, subtract[1]};
  assign in2 = {adder_in2_1s, subtract[1]};
  assign {adder_carry_out, result_frac_intermediate, grs_intermediate, add_sub_carry_in} = in1 + in2;
  assign {result_frac[0], grs_add} = {result_frac_intermediate, grs_intermediate} ^ {(FRAC_WIDTH+GRS_WIDTH+3){~adder_carry_out & subtract[1]}};
  //subtract && adder_carry_out = 1 if subtract and in1 > in2
                              //= 0 if subtract and in1 < in2
  assign output_zero = ~|expo_diff[1] & ~|result_frac_intermediate;
  assign result_sign[0] = output_zero & (subtract[1]) ? zero_result_sign[1] : (~adder_carry_out & subtract[1]) ^ rs1_sign[1]; 
  //assign result_sign[0] = (~adder_carry_out & subtract[1]) ^ rs1_sign[1]; 
  assign result_expo[0] = output_zero ? '0 : rs1_expo[1];
  
  //calculate clz and write-back
  logic [EXPO_WIDTH-1:0] clz, clz_with_prepended_0s, left_shift_amt;
  generate if (FRAC_WIDTH+2 <= 32) begin
    clz frac_clz (
      .clz_input (32'(result_frac[1])),
      .clz (clz_with_prepended_0s[4:0])
    );
    assign left_shift_amt = clz_with_prepended_0s - (32 - (FRAC_WIDTH + 1));
  end else begin
    clz_tree frac_clz (
      .clz_input (64'(result_frac[1])),
      .clz (clz_with_prepended_0s[5:0])
    );
    assign left_shift_amt = clz_with_prepended_0s - (64 - (FRAC_WIDTH + 1));
  end endgenerate

  logic [FLEN-1:0] special_case_results[1:0];
  logic output_special_case[1:0];
  always_comb begin
    if(output_inf[2]) begin
      special_case_results[0] = {result_sign[1], {(EXPO_WIDTH){1'b1}}, {(FRAC_WIDTH){1'b0}}}; 
      output_special_case[0] = 1;
    end else if (output_QNaN[2]) begin 
      special_case_results[0] = CANONICAL_NAN;
      output_special_case[0] = 1;
    end else begin
      special_case_results[0] = '0;
      output_special_case[0] = 0;
    end
  end
 
  //output
  /* verilator lint_off UNOPTFLAT */
  logic advance_stage [3:0] ;
  assign advance_stage[0] = ~done[0] | advance_stage[1];
  //assign advance_stage[1] = ~done[1] | advance_stage[2];
  assign advance_stage[1] = fp_wb.ack | ~fp_wb.done;//~done[2] | advance_stage[3];
  /* verilator lint_on UNOPTFLAT */

  assign issue.ready = advance_stage[0]; //FADD module is ready when first pipeline stage is empty
  assign fp_wb.done = done[1];
  assign fp_wb.id = id[1];
  assign fp_wb.fflags = {invalid_operation[2], 3'b0, inexact[2]};
  assign fp_wb.rm = rm[2];
  assign fp_wb.carry = result_frac[1][FRAC_WIDTH+2];
  assign fp_wb.safe = result_frac[1][FRAC_WIDTH+1];
  assign fp_wb.hidden = result_frac[1][FRAC_WIDTH];
  assign fp_wb.grs = grs;
  assign fp_wb.clz = left_shift_amt;
  assign fp_wb.rd = output_special_case[0] ? special_case_results[0] : 
                                             {result_sign[1], result_expo[1], result_frac[1][FRAC_WIDTH-1:0]};

  //pipeline 
  always_ff @ (posedge clk) begin 
    if (advance_stage[0]) begin
      done[0] <= issue.new_request;
      id[0] <= issue.id;
      rm[1] <= rm[0];

      temp_rs1_sign[1] <= temp_rs1_sign[0];
      temp_rs2_sign[1] <= temp_rs2_sign[0];
      temp_rs1_expo[1] <= temp_rs1_expo[0];
      temp_rs2_expo[1] <= temp_rs2_expo[0];
      temp_rs1_frac[1] <= temp_rs1_frac[0];
      temp_rs2_frac[1] <= temp_rs2_frac[0];
      temp_rs1_hidden[1] <= temp_rs1_hidden[0];
      temp_rs2_hidden[1] <= temp_rs2_hidden[0];

      fp_add_grs_r <= fp_add_grs;

      expo_diff[1] <= expo_diff[0];
      expo_diff_larger_than_frac_width[1] <= expo_diff_larger_than_frac_width[0];
      rs2_grs_sticky_bit[1] <= rs2_grs_sticky_bit[0];
      subtract[1] <= subtract[0];

      rs1_sign[1] <= rs1_sign[0];
      rs1_expo[1] <= rs1_expo[0];
      rs1_frac[1] <= rs1_frac[0];
      rs1_grs[1] <= rs1_grs[0];
      rs1_safe_bit[1] <= rs1_safe_bit[0];

      rs2_sign[1] <= rs2_sign[0];
      rs2_expo[1] <= rs2_expo[0];
      rs2_frac[1] <= rs2_frac[0];
      rs2_grs[1] <= grs_in;
      rs2_safe_bit[1] <= rs2_safe_bit[0];

      rs2_frac_aligned[1] <= rs2_frac_aligned[0];
      rs1_frac_2s[1] <= rs1_frac_2s[0];
      rs2_frac_2s[1] <= rs2_frac_2s[0];

      zero_result_sign[1] <= zero_result_sign[0];
      invalid_operation[1] <= invalid_operation[0];
      output_QNaN[1] <= output_QNaN[0];
      output_inf[1] <= output_inf[0];
      inexact[1] <= inexact[0];//|fp_add_grs;

    end

    //adder -> norm
    if (advance_stage[1]) begin
      done[1] <= done[0];
      id[1] <= id[0];
      rm[2] <= rm[1];
      result_sign[1] <= result_sign[0];
      result_expo[1] <= result_expo[0];
      result_frac[1] <= result_frac[0];
      grs <= grs_add;
      invalid_operation[2] <= invalid_operation[1];
      output_QNaN[2] <= output_QNaN[1];
      output_inf[2] <= output_inf[1];
      inexact[2] <= inexact[1];
    end

    //norm -> round1
    if (advance_stage[2]) begin
      done[2] <= done[1];
      id[2] <= id[1];
      rm[3] <= rm[2];
      result_sign_norm[1] <= result_sign_norm[0];
      result_sign_norm[2] <= result_sign_norm[1];
      result_expo_norm[1] <= result_expo_norm[0];
      result_expo_norm[2] <= result_expo_norm[1];
      result_frac_norm[1] <= result_frac_norm[0];    
      result_frac_norm[2] <= result_frac_norm[1];    
      inexact[3] <= inexact[2];
      invalid_operation[3] <= invalid_operation[2];
      output_QNaN[3] <= output_QNaN[2];
      output_inf[3] <= output_inf[2];
      grs_round <= grs_norm;

    end

    //norm -> round2
    if (advance_stage[3]) begin
      done[3] <= done[2];
      id[3] <= id[2];
      //grs_round_compressed[1] <= grs_round_compressed[0];
      output_inf[4] <= output_inf[3];
      invalid_operation[4] <= invalid_operation[2];
      output_QNaN[4] <= output_QNaN[3];
      roundup[1] <= roundup[0];
      special_case_results[1] <= special_case_results[0];
      output_special_case[1] <= output_special_case[0];
      overflow_before_rounding[1] <= overflow_before_rounding[0];
    end
  end

  //assertions
  //rs1_larger_exponent: assert property(@(posedge clk) disable iff(rst)
  //rs1_expo[0] >= rs2_expo[0]);

  //alignment: assert property (@(posedge clk) disable iff(rst)
    //rs1_frac_aligned == rs1_frac[0] && rs2_frac_aligned == (rs2_frac[0] >> (rs1_expo[0] - rs2_expo[0])));

  //result_expo_compare: assert property (@(posedge clk) disable iff(rst)
    //result_expo[0] == rs1_expo[1]);

  //logic [FRAC_WIDTH+1:0] result_frac_assert_same_sign, result_frac_assert_diff_sign_rs1_larger, result_frac_assert_diff_sign_rs2_larger;
  //logic result_sign_assert;
  //logic [FRAC_WIDTH:0] rs1_frac_aligned_r, rs2_frac_aligned_r;
  //logic rs1_NaN, rs2_NaN;
  //assign rs1_NaN = (rs1_expo[0] == '1) && (rs1_frac[0][FRAC_WIDTH-1:0] != '0);
  //assign rs2_NaN = (rs2_expo[0] == '1) && (rs2_frac[0][FRAC_WIDTH-1:0] != '0);

  //always_ff @ (posedge clk) begin
    //if (advance) begin
      //rs1_frac_aligned_r <= rs1_frac_aligned;
      //rs2_frac_aligned_r <= rs2_frac_aligned;
    //end
  //end

  //assign result_frac_assert_same_sign = rs1_frac_aligned_r + rs2_frac_aligned_r;
  //assign result_frac_assert_diff_sign_rs1_larger = rs1_frac_aligned_r - rs2_frac_aligned_r;
  //assign result_frac_assert_diff_sign_rs2_larger = rs2_frac_aligned_r - rs1_frac_aligned_r;
  //always_comb begin
    //if (rs1_sign[1] == rs2_sign[1]) 
    //result_sign_assert = rs1_sign[1];
    //else begin
    //if (rs1_frac_aligned_r >= rs2_frac_aligned_r)
      //result_sign_assert = rs1_sign[1];
    //else 
       //result_sign_assert = rs2_sign[1];
    //end
  //end

  //sanity_check: assert property (@(posedge clk) disable iff(rst)
    //(rs1_frac_aligned_r == $past(rs1_frac_aligned,1) && rs2_frac_aligned_r == $past(rs2_frac_aligned,1)));

  //result_frac_same_sign: assert property (@(posedge clk) disable iff(rst)
    //(!rs1_NaN && !rs2_NaN && fn7 == FADD && rs1_sign[0] == rs2_sign[0]) |-> ##1 result_frac[0] == result_frac_assert_same_sign);

  //result_frac_diff_sign_rs1_larger: assert property (@(posedge clk) disable iff(rst)
    //(!rs1_NaN && !rs2_NaN && fn7 == FADD && rs1_sign[0] != rs2_sign[0] && rs1_frac_aligned >= rs2_frac_aligned) |-> ##1 result_frac[0] == result_frac_assert_diff_sign_rs1_larger);

  //result_frac_diff_sign_rs2_larger: assert property (@(posedge clk) disable iff(rst)
    //(!rs1_NaN && !rs2_NaN && fn7 == FADD && rs1_sign[0] != rs2_sign[0] && rs1_frac_aligned < rs2_frac_aligned) |-> ##1 result_frac[0] == result_frac_assert_diff_sign_rs2_larger);

  //resul_sign_compare: assert property (@(posedge clk) disable iff(rst)
    //rs1_NaN && !rs2_NaN |-> ##1result_sign[0] == result_sign_assert);
endmodule
