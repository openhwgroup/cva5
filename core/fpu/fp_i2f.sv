import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module fp_i2f (
  input logic clk,
  input logic rst,
  unit_issue_interface.unit issue,
  input logic [XLEN-1:0] rs1_int,
  input logic [FLEN-1:0] rs1_float,
  input logic [2:0] rm,
  input logic [3:0] special_case,
  input logic is_signed,
  input logic is_f2f,
  input logic is_d2s,
  fp_unit_writeback_interface.unit fp_wb
  );
  
  id_t  id;
  logic done;
  logic [2:0] rm_r;

  ///////////////////////////////
  //Integer to Double Conversion
  logic                            rs1_zero [1:0];
  logic [XLEN-1:0]                 rs1_int_abs [1:0];
  logic [EXPO_WIDTH-1:0]           i2f_int_width_minus_1;
  logic [4:0]                      clz [1:0];
  fp_shift_amt_t                   i2f_clz;
  logic                            i2f_sign[1:0];
  logic [EXPO_WIDTH-1:0]           i2f_expo;
  logic [FRAC_WIDTH-1:0]           i2f_frac;
  logic [2:0]                      i2f_grs;
  logic [FLEN-1:0]                 i2f_rd;
  logic [4:0]                      i2f_fflags;

  //get abs(int) 
  logic [XLEN-1:0] neg_i2f_rs1;
  assign neg_i2f_rs1 = -rs1_int;
  always_comb begin
    if (is_signed == 1 && rs1_int[XLEN-1] == 1) begin
      i2f_sign[0] = 1'b1; 
      rs1_int_abs[0] = neg_i2f_rs1;
    end else begin 
      i2f_sign[0] = 1'b0; 
      rs1_int_abs[0] = rs1_int;          
    end
  end
  assign rs1_zero[0] = ~|rs1_int;

  // find input integer clz
  clz clz_inst(.clz_input(rs1_int_abs[1]), .clz(clz[1]));

  ///////////////////////////////////////
  // I2F
  assign i2f_int_width_minus_1 = (XLEN - 1) - EXPO_WIDTH'(clz[1]); //the number of valid bits (excluding leaeding 0s) in the integer minus 1;

  // handle reduced precision < XLEN
  generate if (FRAC_WIDTH >= XLEN) begin
    assign i2f_frac = {{(FRAC_WIDTH-XLEN){1'b0}}, rs1_int_abs[1]};
    assign i2f_grs = 0; //the entire integer will fit in mantissa field
    assign i2f_clz = FRAC_WIDTH - i2f_int_width_minus_1;
    assign i2f_fflags = 0; 
  end else begin
    assign i2f_frac = rs1_int_abs[1][XLEN-1-:FRAC_WIDTH];
    assign i2f_grs = {rs1_int_abs[1][XLEN-1-FRAC_WIDTH-:2], |rs1_int_abs[1][XLEN-1-FRAC_WIDTH-2:0]};
    assign i2f_clz = $bits(fp_shift_amt_t)'(clz[1]) + 1;
    assign i2f_fflags = 0; //|i2f_grs; breaking compliance anyways
  end endgenerate
  assign i2f_expo = (FRAC_WIDTH + BIAS) & {{EXPO_WIDTH{~rs1_zero[1]}}};
  assign i2f_rd = {i2f_sign[1], i2f_expo, i2f_frac};

  ///////////////////////////////////////
  //Floating Point Format Conversion
  logic [FLEN-1:0] DS_rd;
  logic [2:0] DS_grs;
  logic is_DS;

  // Single <-> Double
  generate if (FRAC_WIDTH == 52) begin
  fp_DS S2D_D2S_CONV (
    .clk (clk),
    .advance (advance),
    .rs1_fp (rs1_float),
    .rs1_special_case (special_case),
    .is_D2S (is_f2f&is_d2s),
    .rd (DS_rd),
    .grs (DS_grs)
  );
  end endgenerate

  ///////////////////////////////////////
  // control signals
  logic advance;
  assign advance = fp_wb.ack | ~fp_wb.done;
  //registers
  always_ff @ (posedge clk) begin 
    if (advance) begin 
      done <= issue.new_request;
      id <= issue.id;
      rm_r <= rm;

      i2f_sign[1] <= i2f_sign[0];
      rs1_zero[1] <= rs1_zero[0];
      rs1_int_abs[1] <= rs1_int_abs[0];
      //clz[1] <= clz[0]; 
      is_DS <= is_f2f;
    end
  end

  ///////////////////////////////////////
  //mux outputs
  logic [2:0] DS_rm_out;
  generate if (FLEN == 64) 
    assign DS_rm_out = (rm_r == 3'b010) & ~DS_rd[XLEN-1] ? 3'b001 : ((rm_r == 3'b011) & ~DS_rd[XLEN-1] ? 3'b010 : rm_r);
  else 
    assign DS_rm_out = rm_r;
  endgenerate

  always_comb begin
    fp_wb.done = done;
    fp_wb.id = id;
    if (is_DS) begin// is_f2f[1])
      fp_wb.clz = 0;
      fp_wb.rd = DS_rd;//{DS_sign, DS_expo, DS_frac};
      fp_wb.grs = DS_grs;
      fp_wb.fflags = {4'b0, |DS_grs};
      fp_wb.hidden = 1;
      fp_wb.rm = DS_rm_out;
    end else begin
      fp_wb.clz = i2f_clz;
      fp_wb.rd = i2f_rd;
      fp_wb.grs = i2f_grs;
      fp_wb.fflags = i2f_fflags;
      fp_wb.hidden = 0;
      fp_wb.rm = rm_r;
    end
  end

endmodule : fp_i2f
