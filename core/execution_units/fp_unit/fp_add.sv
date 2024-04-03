/*
 * Copyright © 2019-2023 Yuhui Gao, Chris Keilbart, Lesley Shannon
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * Initial code developed under the supervision of Dr. Lesley Shannon,
 * Reconfigurable Computing Lab, Simon Fraser University.
 *
 * Author(s):
 *             Yuhui Gao <yuhuig@sfu.ca>
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module fp_add

    import cva5_config::*;
    import cva5_types::*;
    import fpu_types::*;

    (
        input logic clk,
        input logic rst,
        input fp_add_inputs_t args,
        unit_issue_interface.unit issue,
        fp_intermediate_wb_interface.unit wb
    );

    logic advance_to_add;
    logic advance_to_final;

    /////////////////////////////////////////////
    //Cycle 1
    //Swap and align arguments
    //Also detect special cases
    logic temp_rs2_sign;
    assign temp_rs2_sign = args.add ? args.rs2.d.sign : ~args.rs2.d.sign;

    //Special case handling
    logic nv[2:0];
    logic inf[2:0];
    logic qnan[1:0];
    logic subtract[2:0];
    logic zero_result_sign[2:0];
    logic inf_sign[2:0];

    //SNAN or "magnitude subtraction of infinities"
    assign nv[0] = args.rs1_special_case.snan | args.rs2_special_case.snan | (args.rs1_special_case.inf & args.rs2_special_case.inf & (args.rs1.d.sign ^ temp_rs2_sign));
    assign qnan[0] = args.rs1_special_case.snan | args.rs1_special_case.qnan | args.rs2_special_case.snan | args.rs2_special_case.qnan | nv[0];
    assign inf[0] = (args.rs1_special_case.inf | args.rs2_special_case.inf) & ~qnan[0];
    assign inf_sign[0] = args.rs1_special_case.inf ? args.rs1.d.sign : temp_rs2_sign;
    assign subtract[0] = args.rs1.d.sign ^ temp_rs2_sign;
    assign zero_result_sign[0] = args.rm == 3'b010;

    //Swap arguments, moving input with larger expo to rs1
    logic rs1_sign[2:0];
    expo_d_t rs1_expo[2:0];
    logic rs1_expo_overflow[2:0];
    logic[FRAC_WIDTH+1:0] rs1_frac[1:0];
    logic[FRAC_WIDTH+1:0] rs2_frac[0:0];
    grs_t rs1_grs[1:0];
    grs_t temp_rs2_grs;
    
    always_comb begin
        if (~args.swap) begin
            rs1_sign[0] = args.rs1.d.sign;
            rs1_expo_overflow[0] = args.rs1_expo_overflow;
            rs1_expo[0] = args.rs1.d.expo;
            rs1_frac[0] = {args.rs1_safe, args.rs1_hidden, args.rs1.d.frac};
            rs1_grs[0] = args.fp_add_grs;

            rs2_frac[0] = {args.rs2_safe, args.rs2_hidden, args.rs2.d.frac};
            temp_rs2_grs = '0;
        end else begin
            rs1_sign[0] = temp_rs2_sign;
            rs1_expo_overflow[0] = 1'b0;
            rs1_expo[0] = args.rs2.d.expo;
            rs1_frac[0] = {args.rs2_safe, args.rs2_hidden, args.rs2.d.frac};
            rs1_grs[0] = '0;

            rs2_frac[0] = {args.rs1_safe, args.rs1_hidden, args.rs1.d.frac};
            temp_rs2_grs = args.fp_add_grs;
        end
    end

    //Alignment through shifting
    logic shift_sticky[1:0];
    logic[FRAC_WIDTH+1:0] rs2_frac_aligned[1:0];
    grs_t rs2_grs[1:0];
    logic[FRAC_WIDTH+GRS_WIDTH+1:0] shifter_input;
    
    assign shifter_input = {rs2_frac[0], temp_rs2_grs};
    assign {rs2_frac_aligned[0], rs2_grs[0]} = shifter_input >> args.expo_diff;
    
    //If the shift amount is too large, bits might get shifted out so this checks for them
    fp_sticky_tracking #(.INPUT_WIDTH($bits(shifter_input)), .SHIFT_WIDTH(EXPO_WIDTH+1)) sticky_tracking (
        .shifter_input(shifter_input),
        .shift_amount(args.expo_diff),
        .sticky_bit(shift_sticky[0])
    );

    //Pipeline to next stage
    logic valid_r;
    rm_t rm_r;
    id_t id_r;
    logic d2s_r;
    
    assign advance_to_add = ~valid_r | advance_to_final;

    always_ff @(posedge clk) begin
        if (rst)
            valid_r <= 0;
        else if (advance_to_add)
            valid_r <= issue.new_request;

        if (advance_to_add) begin
            d2s_r <= args.single;
            id_r <= issue.id;
            rm_r <= args.rm;

            nv[1] <= nv[0];
            qnan[1] <= qnan[0];
            inf[1] <= inf[0];
            inf_sign[1] <= inf_sign[0];
            subtract[1] <= subtract[0];
            zero_result_sign[1] <= zero_result_sign[0];

            rs1_sign[1] <= rs1_sign[0];
            rs1_expo[1] <= rs1_expo[0];
            rs1_expo_overflow[1] <= rs1_expo_overflow[0];
            rs1_frac[1] <= rs1_frac[0];
            rs1_grs[1] <= rs1_grs[0];

            rs2_grs[1] <= rs2_grs[0];
            rs2_frac_aligned[1] <= rs2_frac_aligned[0];
            shift_sticky[1] <= shift_sticky[0];
        end
    end


    /////////////////////////////////////////////
    //Cycle 2
    //Perform the sign-magnitude mantissa addition
    //Coded as an adder followed by negation, but the tools will transform this into two parallel additions with a muxing of the result
    //Negation is only required for different sign addition that returns a negative result
    logic[FRAC_WIDTH+GRS_WIDTH+2:0] adder_in1;
    logic[FRAC_WIDTH+GRS_WIDTH+2:0] adder_in2, adder_in2_1s;
    logic carry_add;
    grs_t grs_add;
    logic[FRAC_WIDTH+1:0] frac_add;
    logic sticky_add;
    logic[1+GRS_WIDTH+FRAC_WIDTH+2-1:0] sum;
    logic[1+GRS_WIDTH+FRAC_WIDTH+2-1:0] sum_final;

    assign adder_in2 = {rs2_frac_aligned[1], rs2_grs[1], shift_sticky[1]};
    assign adder_in2_1s = adder_in2 ^ {(FRAC_WIDTH+GRS_WIDTH+3){subtract[1]}};
    assign adder_in1 = {rs1_frac[1], rs1_grs[1], 1'b0};

    assign {carry_add, sum} = adder_in1 + adder_in2_1s + {{(FRAC_WIDTH+GRS_WIDTH+2){1'b0}}, subtract[1]};
    //subtract & ~carry_add = 1 if subtract and adder_in1 > adder_in2_1s, 0 if adder_in1 < adder_in2_1s
    assign sum_final = ~carry_add & subtract[1] ? -sum : sum;
    assign {frac_add, grs_add, sticky_add} = sum_final;


    //Pipeline to next stage
    logic[FRAC_WIDTH+1:0] result_frac;
    grs_t result_grs;
    logic result_carry_out;
    logic output_special;
    logic result_expo_zero;

    assign advance_to_final = wb.ack | ~wb.done;

    always_ff @ (posedge clk) begin
        if (rst)
            wb.done <= 0;
        else if (advance_to_final)
            wb.done <= valid_r;

        if (advance_to_final) begin
            wb.d2s <= d2s_r;
            wb.id <= id_r;
            wb.rm <= rm_r;

            nv[2] <= nv[1];
            inf[2] <= inf[1];
            inf_sign[2] <= inf_sign[1];
            output_special <= inf[1] | qnan[1];
            subtract[2] <= subtract[1];
            zero_result_sign[2] <= zero_result_sign[1];

            rs1_sign[2] <= rs1_sign[1];
            rs1_expo[2] <= rs1_expo[1];
            result_expo_zero <= ~|rs1_expo[1];
            rs1_expo_overflow[2] <= rs1_expo_overflow[1];

            result_frac <= frac_add;
            result_carry_out <= carry_add;
            result_grs[GRS_WIDTH-1:1] <= grs_add[GRS_WIDTH-1:1];
            result_grs[0] <= grs_add[0] | sticky_add; //Don't lose the sticky
        end
    end


    /////////////////////////////////////////////
    //Cycle 3
    //Find CLZ and determine shift amount
    //Override on special case and drive outputs
    logic result_zero;
    logic[$clog2(FRAC_WIDTH+1+GRS_WIDTH)-1:0] clz_count;
    clz #(.WIDTH(FRAC_WIDTH+1+GRS_WIDTH)) shift_clz (
        .clz_input({result_frac[FRAC_WIDTH:0], result_grs}),
        .clz(clz_count),
        .zero(result_zero)
    );

    //Determine exponent and sign
    logic carry_set;
    logic output_zero;
    logic result_sign;
    logic result_expo_overflow;
    expo_d_t result_expo;
    fp_shift_amt_t clz_shift_amt;

    assign carry_set = ~subtract[2] & result_carry_out;
    assign output_zero = result_zero & ~result_frac[FRAC_WIDTH+1] & ~carry_set;
    assign result_sign = output_zero & subtract[2] ? zero_result_sign[2] : (~result_carry_out & subtract[2]) ^ rs1_sign[2];
    assign result_expo_overflow = ~output_zero & rs1_expo_overflow[2];
    always_comb begin
        clz_shift_amt = '0;
        clz_shift_amt[$bits(clz_count)-1:0] = clz_count;

        if (output_zero)
            result_expo = '0;
        else if (result_expo_zero & (result_frac[FRAC_WIDTH] | carry_set | result_frac[FRAC_WIDTH+1])) //Subnormal promotion
            result_expo = 1; //Will be added to the right shift amount to get the correct exponent
        else if (clz_shift_amt >= rs1_expo[2] & ~result_expo_zero & ~result_frac[FRAC_WIDTH+1] & ~carry_set) //Subnormal demotion
            result_expo = rs1_expo[2] - 1;
        else
            result_expo = rs1_expo[2];
    end

    fp_t special_result;
    always_comb begin
        if (inf[2]) begin
            special_result.d.sign = inf_sign[2];
            special_result.d.expo = '1;
            special_result.d.frac = '0;
        end
        else //qnan
            special_result.raw = CANONICAL_NAN;
    end

    //Writeback
    assign issue.ready = advance_to_add;
    assign wb.fflags.nv = nv[2];
    assign wb.fflags.of = 0;
    assign wb.fflags.uf = 0;
    assign wb.fflags.dz = 0;
    assign wb.fflags.nx = 0; //Will be set by normalization
    assign wb.carry = ~output_special & carry_set;
    assign wb.safe = result_frac[FRAC_WIDTH+1] & ~output_special;
    assign wb.hidden = result_frac[FRAC_WIDTH] | output_special;
    assign wb.grs = output_special ? '0 : result_grs;
    always_comb begin
        wb.clz = '0;
        if (~output_zero & ~output_special)
            wb.clz[$bits(clz_count)-1:0] = clz_count;
        
        if (output_special)
            wb.rd = special_result;
        else begin
            wb.rd.d.sign = result_sign;
            wb.rd.d.expo = result_expo;
            wb.rd.d.frac = result_frac[FRAC_WIDTH-1:0];
        end
    end
    assign wb.expo_overflow = result_expo_overflow & ~output_special;
    assign wb.subnormal = ~|result_expo & ~output_special & ~wb.right_shift & ~result_expo_overflow;
    assign wb.right_shift = ~output_special & (result_frac[FRAC_WIDTH+1] | carry_set);
    assign wb.right_shift_amt = {{(EXPO_WIDTH-2){1'b0}}, carry_set, result_frac[FRAC_WIDTH+1] & ~carry_set}; //Either 1 or 2
    assign wb.ignore_max_expo = output_special;

endmodule
