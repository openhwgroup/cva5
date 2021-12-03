import taiga_config::*;
import taiga_types::*;
import l2_config_and_types::*;
import fpu_types::*;

//TODO: underflow results in a 0: can deliver rounded subnormal instead
module fp_mul_madd_fused (
  input logic clk,
  input logic rst,
  input fp_madd_inputs_t fp_madd_inputs,
  unit_issue_interface.unit issue,
  //output fp_unit_writeback_t fp_wb,
  fp_unit_writeback_interface.unit fp_wb,
  //output [4:0] fflags,
  output fma_mul_outputs_t fma_mul_outputs
  );

  parameter BIAS = {1'b0, {(EXPO_WIDTH-1){1'b1}}};
  logic [FLEN-1:0]               rs1;
  logic [FLEN-1:0]               rs2;
  logic [2:0]                    rm [4:0];
  logic [6:0]                    opcode [3:0];
  logic [2:0]                    instruction [3:0];

  logic                          rs1_hidden_bit;
  logic                          rs1_sign [2:0];
  logic [EXPO_WIDTH-1:0]         rs1_expo [2:0];
  logic [FRAC_WIDTH:0]           rs1_frac [2:0];

  logic                          rs2_hidden_bit;
  logic                          rs2_sign [2:0];
  logic [EXPO_WIDTH-1:0]         rs2_expo [2:0];
  logic [FRAC_WIDTH:0]           rs2_frac [2:0];

  logic                          rs1_zero;
  logic                          rs2_zero;
  logic                          rs1_inf;
  logic                          rs2_inf;
  logic                          rs1_subnormal;
  logic                          rs2_subnormal;
  logic                          rs1_NaN;
  logic                          rs2_NaN;

  logic                          result_sign [1:0];
  logic [EXPO_WIDTH:0]           result_expo [1:0];
  logic [EXPO_WIDTH:0]           result_expo_intermediate;
  logic [FRAC_WIDTH+1:0]         result_frac [1:0];
  logic [2*FRAC_WIDTH+2-1:0]     result_frac_intermediate, result_frac_upper[1:0], result_frac_upper_shifted, result_frac_lower[1:0];

  logic                          result_sign_norm [2:0];
  logic [EXPO_WIDTH-1:0]         result_expo_norm [2:0];
  logic [FRAC_WIDTH+1:0]         result_frac_norm [2:0];

  logic [FRAC_WIDTH-1:0]         residual_bits;
  //grs_t                          residual_bits;
  grs_t                          grs [1:0];
  grs_t                          grs_norm;
  grs_t                          grs_round;

  logic [FLEN-1:0]               result;
  logic [FLEN-1:0]               result_if_overflow[1:0];
  logic                          sign_round_out;
  logic [EXPO_WIDTH-1:0]         expo_round_out;
  logic [FRAC_WIDTH:0]           frac_round_out;
  logic                          safe_bit_round;
  logic [FRAC_WIDTH+1:0]         frac_round_intermediate;
  logic                          underflowFlg, overflowFlg, inexactFlg;
  logic                          underflowExp, overflowExp, inexactExp;
  logic                          roundup[1:0]; 
  logic                          output_QNaN [4:0];
  logic                          invalid_operation [4:0];
  logic                          output_inf[4:0];
  logic                          output_zero [4:0];
  logic                          overflow_before_rounding [2:0];
  logic                          done [3:0];
  id_t                           id [3:0];
  fp_unit_writeback_t            fma_mul_wb;
  logic [FLEN-1:0]               rs3 [3:0];
  logic                          rs3_hidden_bit[3:0];
  logic [3:0]                    rs3_special_case [3:0];
  logic [EXPO_WIDTH:0]           expo_diff;
  logic [EXPO_WIDTH:0]           expo_diff_negate;
 
  assign rs1 = fp_madd_inputs.rs1;
  assign rs2 = fp_madd_inputs.rs2;
  assign rs3[0] = fp_madd_inputs.rs3;
  assign rs3_hidden_bit[0] = fp_madd_inputs.rs3_hidden_bit;
  assign rs3_special_case[0] = fp_madd_inputs.rs3_special_case;
  assign rm[0] = fp_madd_inputs.rm;
  assign opcode[0] = fp_madd_inputs.op;
  assign instruction[0] = fp_madd_inputs.instruction;
  
  //unpacking
  assign rs1_sign[0] = rs1[FLEN-1];
  assign rs1_expo[0] = rs1[FLEN-2:FRAC_WIDTH];
  assign rs1_hidden_bit = fp_madd_inputs.rs1_hidden_bit;
  assign rs1_frac[0] = {rs1_hidden_bit, rs1[FRAC_WIDTH-1:0]};
  assign rs2_sign[0] = rs2[FLEN-1];
  assign rs2_expo[0] = rs2[FLEN-2:FRAC_WIDTH];
  assign rs2_hidden_bit = fp_madd_inputs.rs2_hidden_bit;
  assign rs2_frac[0] = {rs2_hidden_bit, rs2[FRAC_WIDTH-1:0]}; 

  //special cases 
  assign rs1_subnormal = ~rs1_hidden_bit;
  assign rs2_subnormal = ~rs2_hidden_bit;
  assign rs1_zero = fp_madd_inputs.rs1_special_case[0];//rs1_subnormal && (rs1_frac[0][FRAC_WIDTH-1:0] == '0);
  assign rs2_zero = fp_madd_inputs.rs2_special_case[0];//rs2_subnormal && (rs2_frac[0][FRAC_WIDTH-1:0] == '0);
  assign rs1_inf = fp_madd_inputs.rs1_special_case[3];//(rs1_expo[0] == '1) && (rs1_frac[0][FRAC_WIDTH-1:0] == '0);
  assign rs2_inf = fp_madd_inputs.rs2_special_case[3];//(rs2_expo[0] == '1) && (rs2_frac[0][FRAC_WIDTH-1:0] == '0);
  assign rs1_NaN = |fp_madd_inputs.rs1_special_case[2:1];//(rs1_expo[0] == '1) && (rs1_frac[0][FRAC_WIDTH-1:0] != '0);
  assign rs2_NaN = |fp_madd_inputs.rs2_special_case[2:1];//(rs2_expo[0] == '1) && (rs2_frac[0][FRAC_WIDTH-1:0] != '0);
  assign invalid_operation[0] = (((rs1_zero & rs2_inf) | (rs1_inf & rs2_zero)) & rs2 != CANONICAL_NAN)
                              | (rs1 == SNAN) | (rs2 == SNAN); 
  assign output_QNaN[0] = invalid_operation[0] | rs1_NaN | rs2_NaN;
  assign output_inf[0] = ((rs1_inf & ~rs2_zero) | (~rs1_zero & rs2_inf)) & ~output_QNaN[0];
  assign output_zero[0] = (rs1_zero | rs2_zero) & ~output_QNaN[0];

  //multiplication
  //TODO: use DSP's pattern detect for zero result detection
  (* use_dsp = "no" *) unsigned_multiplier #(.WIDTH(FRAC_WIDTH+1)) mantissa_mul (
    .clk(clk),
    .rst(rst),
    .advance1(advance_stage[0]),
    .advance2(advance_stage[1]),
    .rs1(rs1_frac[0]),
    .rs2(rs2_frac[0]),
    .out(result_frac_intermediate)
  );

  always_comb begin 
    result_sign[0] = rs1_sign[2] ^ rs2_sign[2];
    result_expo_intermediate = rs1_expo[2] + rs2_expo[2];
    result_expo[0] = result_expo_intermediate > (EXPO_WIDTH+1)'(BIAS) ? result_expo_intermediate - BIAS : '0; //MSB is used to detect overflow
    result_frac[0] = result_frac_intermediate[2*FRAC_WIDTH+2-1-:(2+FRAC_WIDTH)]; // {safe_bit, hidden_bit, fraction}
    residual_bits = result_frac_intermediate[0+:FRAC_WIDTH]; // bottom bits preserved for rounding
    grs[0] = {residual_bits[FRAC_WIDTH-1-:2], |residual_bits[FRAC_WIDTH-3:0]};
  end

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
  //pre-mux special case results
  always_comb begin
    if(output_inf[3]) begin
      special_case_results[0] = {result_sign[1], {(EXPO_WIDTH){1'b1}}, {(FRAC_WIDTH){1'b0}}}; 
      output_special_case[0] = 1;
    end else if (output_QNaN[3]) begin 
      special_case_results[0] = CANONICAL_NAN;
      output_special_case[0] = 1;
    end else if (output_zero[3]) begin
      special_case_results[0] = {result_sign[1], (FLEN-1)'(0)};
      output_special_case[0] = 1;
    end else begin
      special_case_results[0] = {result_sign[1], (FLEN-1)'(0)};
      output_special_case[0] = 0;
    end
  end

  /* verilator lint_off UNOPTFLAT */
  logic advance_stage [3:0] ;
  assign advance_stage[0] = ~done[0] | advance_stage[1];
  assign advance_stage[1] = ~done[1] | advance_stage[2];
  //assign advance_stage[2] = ~done[2] | advance_stage[3];
  assign advance_stage[2] = fp_wb.ack | ~fp_wb.done;
  /* verilator lint_on UNOPTFLAT */

  //writeback
  assign issue.ready = advance_stage[0];
  assign fp_wb.done = done[2];
  assign fp_wb.id = id[2];
  //assign fp_wb.fflags = {invalid_operation[4], 3'b0, |grs_round_compressed[0]};
  assign fp_wb.fflags = {invalid_operation[3], 4'b0};//, |grs[1]};
  assign fp_wb.carry = 1'b0;
  assign fp_wb.safe = result_frac[1][FRAC_WIDTH+1];
  assign fp_wb.hidden = result_frac[1][FRAC_WIDTH];
  assign fp_wb.grs = grs[1];
  assign fp_wb.rm = rm[3];
  assign fp_wb.clz = left_shift_amt;
  assign fp_wb.rd = output_special_case[0] ? special_case_results[0] : 
                                             {result_sign[1], result_expo[1][EXPO_WIDTH-1:0], result_frac[1][FRAC_WIDTH-1:0]};

  //FMADD outputs 
  //assign fma_mul_wb.rd = {result_sign_norm[0], result_expo_norm[0], result_frac_norm[0][0+:FRAC_WIDTH]};
  assign fma_mul_outputs.is_fma = done[1] & instruction[2][2];
  assign fma_mul_wb.rd = {result_sign[0], result_expo[0][EXPO_WIDTH-1:0], result_frac[0][FRAC_WIDTH-1-:FRAC_WIDTH]};
  assign fma_mul_outputs.mul_wb_rd_hidden = result_frac[0][FRAC_WIDTH+0];
  assign fma_mul_outputs.mul_wb_rd_safe = result_frac[0][FRAC_WIDTH+1];
  assign fma_mul_wb.done = done[1];
  assign fma_mul_wb.id = id[1];
  assign fma_mul_outputs.mul_wb = fma_mul_wb;
  assign fma_mul_outputs.mul_grs = grs[0];
  assign fma_mul_outputs.mul_op = opcode[2][3];
  assign fma_mul_outputs.add_op = opcode[2][2];
  assign fma_mul_outputs.rs3 = rs3[2];
  assign fma_mul_outputs.rs2_special_case = rs3_special_case[2];
  assign fma_mul_outputs.rs3_hidden_bit = rs3_hidden_bit[2];
  assign fma_mul_outputs.mul_rm = rm[2];
  assign fma_mul_outputs.instruction = instruction[2];
  assign fma_mul_outputs.invalid_operation = invalid_operation[2];
  assign fma_mul_outputs.rs1_special_case = {output_inf[2], 1'b0, output_QNaN[2], output_zero[2]};
  logic [EXPO_WIDTH-1:0] rs3_expo;
  assign rs3_expo = rs3[2][FLEN-2-:EXPO_WIDTH];
  assign expo_diff = result_expo[0] - rs3_expo;
  assign expo_diff_negate = rs3_expo - result_expo[0];
  assign fma_mul_outputs.expo_diff = expo_diff[EXPO_WIDTH] ? expo_diff_negate : expo_diff;
  assign fma_mul_outputs.swap = expo_diff[EXPO_WIDTH];

  always_ff @ (posedge clk) begin 
    // mul1
    if (advance_stage[0]) begin
      done[0] <= issue.new_request;
      id[0] <= issue.id;
      rm[1] <= rm[0];

      rs1_sign[1] <= rs1_sign[0];
      rs1_expo[1] <= rs1_expo[0];
      rs1_frac[1] <= rs1_frac[0];

      rs2_sign[1] <= rs2_sign[0];
      rs2_expo[1] <= rs2_expo[0];
      rs2_frac[1] <= rs2_frac[0];

      rs3[1] <= rs3[0];
      rs3_special_case[1] <= rs3_special_case[0];
      rs3_hidden_bit[1] <= rs3_hidden_bit[0];
      opcode[1] <= opcode[0];
      instruction[1] <= instruction[0];
      invalid_operation[1] <= invalid_operation[0];
      output_QNaN[1] <= output_QNaN[0];
      output_inf[1] <= output_inf[0];
      output_zero[1] <= output_zero[0];
      
    end
    // mul2
    if (advance_stage[1]) begin
      done[1] <= done[0];
      id[1] <= id[0];
      rm[2] <= rm[1];
      rs1_sign[2] <= rs1_sign[1];
      rs1_expo[2] <= rs1_expo[1];
      rs1_frac[2] <= rs1_frac[1];

      rs2_sign[2] <= rs2_sign[1];
      rs2_expo[2] <= rs2_expo[1];
      rs2_frac[2] <= rs2_frac[1];

      grs[1] <= grs[0];
      opcode[2] <= opcode[1];
      rs3[2] <= rs3[1];
      instruction[2] <= instruction[1];
      rs3_hidden_bit[2] <= rs3_hidden_bit[1];
      rs3_special_case[2] <= rs3_special_case[1];
      output_QNaN[2] <= output_QNaN[1];
      invalid_operation[2] <= invalid_operation[1];
      output_inf[2] <= output_inf[1];
      output_zero[2] <= output_zero[1];
     
    end
    //norm
    if (advance_stage[2]) begin
      done[2] <= done[1] & instruction[2][0]; //only FMUL instructions go the FMUL writeback path
      id[2] <= id[1];
      rm[3] <= rm[2];
    
      output_QNaN[3] <= output_QNaN[2];
      invalid_operation[3] <= invalid_operation[2];
      output_inf[3] <= output_inf[2];
      output_zero[3] <= output_zero[2];
      opcode[3] <= opcode[2];
      instruction[3] <= instruction[2];
      rs3[3] <= rs3[2];
      rs3_hidden_bit[3] <= rs3_hidden_bit[2];
      overflow_before_rounding[1] <= overflow_before_rounding[0];
      result_sign[1] <= result_sign[0];
      result_expo[1] <= result_expo[0];
      result_frac[1] <= result_frac[0];
    end
    //round1
    if (advance_stage[3]) begin
      done[3] <= done[2];
      id[3] <= id[2];
      rm[4] <= rm[3];
      invalid_operation[4] <= invalid_operation[3];
      output_QNaN[4] <= output_QNaN[3];
      output_inf[4] <= output_inf[3];
      output_zero[4] <= output_zero[3];
      result_sign_norm[1] <= result_sign_norm[0];
      result_expo_norm[1] <= result_expo_norm[0];
      result_frac_norm[1] <= result_frac_norm[0];
      grs_round <= grs_norm;
    end
  end
endmodule
