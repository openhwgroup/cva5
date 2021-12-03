import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*; 

module fp_cvt_top (
  input logic clk,
  input logic rst,
  input fp_cvt_mv_inputs_t     fp_cvt_mv_inputs,
  unit_issue_interface.unit    issue,
  fp_unit_writeback_interface i2f_wb,
  unit_writeback_interface f2i_wb
  );

  logic f2i_new_request, i2f_new_request;
  logic f2i_done[1:0], i2f_done[1:0];
  id_t i2f_id, i2f_id_out[1:0];
  id_t f2i_id, f2i_id_out[1:0];
  logic [FLEN-1:0]  f2i_rs1;
  logic             f2i_rs1_hidden;
  logic [3:0]       f2i_rs1_special_case;
  logic [XLEN-1:0]  i2f_rs1;
  logic [FLEN-1:0]  rs1_float;
  logic is_signed, is_float[2:0], is_mv, is_f2f[2:0], is_d2s[2:0];
  logic [XLEN-1:0] f2i_int_abs[1:0];
  logic f2i_result_sign[1:0];
  logic [2:0] grs_round, f2i_grs[1:0], i2f_grs[1:0];
  logic invalid_operationFlg[1:0];
  logic i2f_result_sign[1:0];
  logic [EXPO_WIDTH-1:0] i2f_result_expo[1:0];
  logic [FRAC_WIDTH-1:0] i2f_result_frac[1:0];
  logic [2:0] rm[2:0];
  logic sign_round;
  logic lsb_round;
  logic roundup;
  logic [FLEN-1:0] result_if_overflow;
  logic inexactFlg;

  localparam EXPO_WIDTH_SINGLE = 8;
  localparam FRAC_WIDTH_SINGLE = 23;

  assign is_signed = fp_cvt_mv_inputs.is_signed;
  assign is_float[0] = fp_cvt_mv_inputs.is_float;
  assign is_f2f[0] = fp_cvt_mv_inputs.is_f2f;
  assign is_d2s[0] = fp_cvt_mv_inputs.is_d2s; 
  assign rm[0] = fp_cvt_mv_inputs.rm;

  assign f2i_new_request = issue.new_request & is_float[0] & ~is_f2f[0];
  assign f2i_id = issue.id;
  assign f2i_rs1 = fp_cvt_mv_inputs.f2i_rs1;
  assign f2i_rs1_hidden = fp_cvt_mv_inputs.f2i_rs1_hidden;
  assign f2i_rs1_special_case = fp_cvt_mv_inputs.f2i_rs1_special_case;


  fp_f2i f2i(
    .clk(clk),
    .rst(rst),
    .advance (f2i_advance),
    .new_request(f2i_new_request),
    .id(f2i_id),
    .rs1_fp(f2i_rs1),
    .hidden_bit_i(f2i_rs1_hidden),
    .special_case(f2i_rs1_special_case),
    .is_signed(is_signed),
    .f2i_int_abs(f2i_int_abs[0]),
    .result_sign(f2i_result_sign[0]),
    .grs(f2i_grs[0]),
    .done(f2i_done[0]),
    .f2i_id(f2i_id_out[0]),
    .invalid_operationFlg(invalid_operationFlg[0])
  );

  unit_issue_interface i2f_issue();
  assign rs1_float = fp_cvt_mv_inputs.f2i_rs1;
  assign i2f_new_request = issue.new_request & (~is_float[0] | is_f2f[0]);
  assign i2f_id = issue.id;
  assign i2f_rs1 = fp_cvt_mv_inputs.i2f_rs1;
  assign  i2f_issue.new_request = i2f_new_request;
  assign  i2f_issue.id = issue.id;

  fp_i2f i2f (
    .clk(clk),
    .rst(rst),
    .issue(i2f_issue),
    .rs1_int(i2f_rs1),
    .rs1_float(rs1_float),
    .rm (rm[0]),
    .special_case(f2i_rs1_special_case),
    .is_signed(is_signed),
    .is_f2f(is_f2f[0]),
    .is_d2s(is_d2s[0]),
    .fp_wb(i2f_wb)
  );

  assign sign_round = is_float[2] & ~is_f2f[2] ? f2i_result_sign[1] : i2f_result_sign[1];
  assign grs_round = is_float[2] & ~is_f2f[2] ? f2i_grs[1] : i2f_grs[1];
  assign lsb_round = is_float[2] & ~is_f2f[2] ? f2i_int_abs[1][0] : i2f_result_frac[1][0];
  assign inexactFlg = |grs_round ;

  fp_round_simplified round(
    .sign(sign_round),
    .rm(rm[2]),
    .grs(grs_round),
    .lsb(lsb_round),
    .roundup(roundup),
    .result_if_overflow(result_if_overflow)
    );

  //result mux
  logic f2i_done_r;
  assign f2i_wb.rd = f2i_result_sign[1] ? -(f2i_int_abs[1] + XLEN'(roundup)) : (f2i_int_abs[1] + XLEN'(roundup));
  assign f2i_wb.done = f2i_done[1] | f2i_done_r;
  assign f2i_wb.id = f2i_id_out[1];
  assign f2i_wb.fflags = {invalid_operationFlg[1], 3'b0, inexactFlg};

  assign issue.ready = advance;
  logic i2f_advance, f2i_advance, advance;
  assign i2f_advance = i2f_wb.ack | ~i2f_wb.done; 
  assign f2i_advance = f2i_wb.ack | ~f2i_wb.done;
  assign advance = i2f_advance & f2i_advance;
  //registers
  always_ff @ (posedge clk) begin 
    if (f2i_wb.ack)
      f2i_done_r <= 0;
    else if (f2i_done[1])
      f2i_done_r <= 1;

    if (advance) begin
      f2i_done[1] <= f2i_done[0];
      f2i_id_out[1] <= f2i_id_out[0];

      is_float[1] <= is_float[0];
      is_float[2] <= is_float[1];
      rm[1] <= rm[0];
      rm[2] <= rm[1];
      invalid_operationFlg[1] <= invalid_operationFlg[0];

      f2i_grs[1] <= f2i_grs[0];
      f2i_result_sign[1] <= f2i_result_sign[0];
      f2i_int_abs[1] <= f2i_int_abs[0];

      i2f_grs[1] <= i2f_grs[0];
      i2f_result_sign[1] <= i2f_result_sign[0];
      i2f_result_expo[1] <= i2f_result_expo[0];
      i2f_result_frac[1] <= i2f_result_frac[0];
      is_f2f[1] <= is_f2f[0];
      is_f2f[2] <= is_f2f[1];
      is_d2s[1] <= is_d2s[0];
      is_d2s[2] <= is_d2s[1];
    end
  end

endmodule : fp_cvt_top
