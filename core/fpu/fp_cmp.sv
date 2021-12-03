import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module fp_cmp (
  input logic clk,
  input logic rst,
  //FCMP 
  input fp_cmp_inputs_t fp_cmp_inputs,
  unit_writeback_interface cmp_wb,
  //FMIN_MAX
  // input fp_minmax_inputs_t fp_minmax_inputs,
  unit_issue_interface.unit issue,
  fp_unit_writeback_interface.unit minmax_wb
  );

  logic                   done;
  id_t                    id;
  logic [FLEN-1:0]        rs1;
  logic [FLEN-1:0]        rs2;
  logic [2:0]             fn3;        //mode selection
  logic [6:0]             fn7;
  logic                   rs1_hidden_bit;
  logic                   rs2_hidden_bit;

  logic                   rs1_sign;
  logic [EXPO_WIDTH-1:0]  rs1_expo;
  logic [FRAC_WIDTH-1:0]  rs1_frac;
  logic                   rs1_NaN;
  logic                   rs1_inf;
  logic                   rs1_subnormal;
  logic                   rs1_zero;
  logic                   rs2_sign;
  logic [EXPO_WIDTH-1:0]  rs2_expo;
  logic [FRAC_WIDTH-1:0]  rs2_frac;
  logic                   rs2_NaN;
  logic                   rs2_inf;
  logic                   rs2_subnormal;
  logic                   rs2_zero;

  logic                   invalid_cmp;
  logic                   unordered;
  logic                   invalid_minmax;
  logic                   feq;
  logic                   flt_intermediate, flt;
  logic                   fle;
  logic [XLEN-1:0]        result;
  logic                   min_hidden;
  logic                   max_hidden;
  logic                   minmax_hidden;
  logic [FLEN-1:0]        min_result;
  logic [FLEN-1:0]        max_result;
  logic [FLEN-1:0]        minmax_result;
  logic                   is_sign_inj;
  logic                   is_class;
  logic [3:0]             rs1_special_case;
  logic [3:0]             rs2_special_case;
  logic                   sign_inj_hidden;
  logic [FLEN-1:0]        sign_inj_result;
  logic [XLEN-1:0]        class_result;
  logic                   neg_inf;
  logic                   neg_normal;
  logic                   neg_subnormal;
  logic                   neg_zero;
  logic                   pos_zero;
  logic                   pos_subnormal;
  logic                   pos_normal;
  logic                   pos_inf;
  logic                   sNaN;
  logic                   qNaN;

  assign rs1_sign = rs1[FLEN-1];
  assign rs1_expo = rs1[FLEN-2:FRAC_WIDTH];
  assign rs1_frac = rs1[FRAC_WIDTH-1:0];
  assign rs1_subnormal = ~rs1_hidden_bit;//~|rs1_expo;
  assign rs1_inf = rs1_special_case[3];
  assign rs1_NaN = |rs1_special_case[2:1];
  assign rs1_zero = rs1_special_case[0];
  assign rs2_sign = rs2[FLEN-1];
  assign rs2_expo = rs2[FLEN-2:FRAC_WIDTH];
  assign rs2_frac = rs2[FRAC_WIDTH-1:0];
  assign rs2_subnormal = ~rs1_hidden_bit;//~|rs2_expo;
  assign rs2_inf = rs2_special_case[3];
  assign rs2_NaN = |rs2_special_case[2:1];
  assign rs2_zero = rs2_special_case[0];

                    //FLT FLE signaling comparison            FEQ quiet comparison
  assign invalid_cmp = ((fn3 != 3'b010) && (rs1_NaN || rs2_NaN)) || ((fn3 == 3'b010) && (rs1 == SNAN || rs2 == SNAN));
  assign invalid_minmax = (rs1 == SNAN) || (rs2 == SNAN);
  assign unordered = (rs1_NaN | rs2_NaN) & ~is_class;
  
  //FEQ
  assign feq = (rs1_zero && rs2_zero) || ((rs1_sign == rs2_sign) && (rs1_expo == rs2_expo) && (rs1_frac == rs2_frac));
  
  //FLT 
  always_comb begin 
    if (rs1_sign > rs2_sign) begin 
      //rs1 neg, rs2 pos
      flt_intermediate = 1;
    end else if (rs1_sign < rs2_sign) begin 
      //rs1 pos, rs2 neg
      flt_intermediate = 0;
    end else begin 
      //same sign
      case(rs1_sign)    //or rs2_sign, doesnt matter here
        0: begin 
          //both inputs are positive
          if (rs1_expo > rs2_expo) begin 
            flt_intermediate = 0;
          end else if (rs1_expo < rs2_expo) begin 
            flt_intermediate = 1;
          end else begin 
            //same exponent
            if (rs1_frac >= rs2_frac) begin 
              flt_intermediate = 0;
            end else begin 
              flt_intermediate = 1;
            end
          end
        end
        1: begin 
          //both inputs are negative
          if (rs1_expo > rs2_expo) begin 
            flt_intermediate = 1;
          end else if (rs1_expo < rs2_expo) begin 
            flt_intermediate = 0;
          end else begin 
            if (rs1_frac > rs2_frac) begin 
              flt_intermediate = 1;
            end else begin 
              flt_intermediate = 0;
            end
          end
        end
      endcase // rs1_sign
    end
    flt = flt_intermediate & ~(rs1_zero & rs2_zero);
  end
  
  //FLE
  assign fle = flt || feq;
  
  //min max results 
  always_comb begin 
      case({rs1_NaN, rs2_NaN})
        2'b11: begin 
          //both inputs are NaN
          min_result = CANONICAL_NAN;
          min_hidden = 1;
          max_result = CANONICAL_NAN;
          max_hidden = 1;
        end
        2'b10: begin 
          //rs1 == NaN
          min_result = rs2;
          max_result = rs2;
          min_hidden = rs1_hidden_bit;
          max_hidden = rs1_hidden_bit;
        end
        2'b01: begin 
          //rs2 == NaN
          min_result = rs1;
          max_result = rs1;
          min_hidden = rs1_hidden_bit;
          max_hidden = rs1_hidden_bit;
        end
        2'b00: begin
          //both inputs normal
          min_result = (flt == 1) ? rs1 : rs2;
          min_hidden = (flt == 1) ? rs1_hidden_bit : rs2_hidden_bit;
          max_result = (flt == 1) ? rs2 : rs1;
          max_hidden = (flt == 1) ? rs2_hidden_bit : rs1_hidden_bit;
        end
      endcase
  end
  
  //cmp result mux
  always_comb begin 
    if (is_class) 
      result = XLEN'({qNaN, sNaN, pos_inf, pos_normal, pos_subnormal, pos_zero, neg_zero, neg_subnormal, neg_normal, neg_inf});
    else begin
      case(fn3) 
        default: result = {{(XLEN-1){1'b0}},fle};
        3'b001: result = {{(XLEN-1){1'b0}},flt};
        3'b010: result = {{(XLEN-1){1'b0}},feq};
      endcase // fn3
    end
  end
  
  //sign inj results
  always_comb begin 
    sign_inj_hidden = rs1_hidden_bit;
  case(fn3)
    default: sign_inj_result = {rs2_sign, rs1[FLEN-2:0]};
    3'b001:  sign_inj_result = {~rs2_sign, rs1[FLEN-2:0]};
    3'b010:  sign_inj_result = {rs2_sign ^ rs1[FLEN-1], rs1[FLEN-2:0]};
  endcase // rm
  end

  //class results
  assign neg_inf = rs1_sign && rs1_inf;
  assign neg_normal = rs1_sign && !rs1_subnormal;
  assign neg_subnormal = rs1_sign && rs1_subnormal && !rs1_zero;
  assign neg_zero = rs1_sign && rs1_zero;
  assign pos_zero = !rs1_sign && rs1_zero;
  assign pos_subnormal = !rs1_sign && rs1_subnormal && !rs1_zero;
  assign pos_normal = !rs1_sign && !rs1_subnormal;
  assign pos_inf = !rs1_sign && rs1_inf;
  assign sNaN = rs1_special_case[2];//(rs1 == SNAN);               
  assign qNaN = rs1_special_case[1];//(rs1 == CANONICAL_NAN);  


  always_ff @ (posedge clk) begin 
    if (advance) begin
      rs1 <= fp_cmp_inputs.rs1;
      rs2 <= fp_cmp_inputs.rs2;
      rs1_hidden_bit <= fp_cmp_inputs.rs1_hidden_bit;
      rs2_hidden_bit <= fp_cmp_inputs.rs2_hidden_bit;
      fn3 <= fp_cmp_inputs.rm;
      fn7 <= fp_cmp_inputs.fn7;
      done <= issue.new_request;
      id <= issue.id;
      is_sign_inj <= fp_cmp_inputs.is_sign_inj;
      is_class <= fp_cmp_inputs.is_class;
      rs1_special_case <= fp_cmp_inputs.rs1_special_case;
      rs2_special_case <= fp_cmp_inputs.rs2_special_case;
    end
  end
  
  //new taiga
  logic advance_cmp, advance_minmax, advance;
  assign advance_cmp = cmp_wb.ack | ~cmp_wb.done;
  assign advance_minmax = minmax_wb.ack | ~minmax_wb.done;
  assign advance = advance_cmp & advance_minmax;

  assign cmp_wb.rd = unordered ? '0 : result;
  assign cmp_wb.done = done & fn7[6] & ~is_sign_inj;
  assign cmp_wb.id = id;
  assign cmp_wb.fflags = {invalid_cmp, 4'b0};

  assign minmax_result = (fn3[0] == 1) ? max_result : min_result;
  assign minmax_hidden = (fn3[0] == 1) ? max_hidden : min_hidden;
  assign minmax_wb.rd = is_sign_inj ? sign_inj_result : minmax_result;
  assign minmax_wb.hidden = is_sign_inj ? sign_inj_hidden : minmax_hidden;
  assign minmax_wb.done = done & ~fn7[6];
  assign minmax_wb.id = id;
  assign minmax_wb.fflags = {invalid_minmax, 4'b0};
 
  assign issue.ready = advance;

endmodule
