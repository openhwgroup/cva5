/*
 * Copyright © 2019-2023 Yuhui Gao, Lesley Shannon
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

module fp_sqrt

    import cva5_config::*;
    import fpu_types::*;

    (
        input logic clk,
        input logic rst,
        input fp_sqrt_inputs_t args,
        unit_issue_interface.unit issue,
        fp_intermediate_wb_interface.unit wb
    );

    //Hidden + GRS + 1 (because without the +1 it gave the wrong sticky bit in certain cases)
    unsigned_sqrt_interface #(.DATA_WIDTH(FRAC_WIDTH+5)) sqrt();

    ////////////////////////////////////////////////////
    //Implementation
    //Iterative square root core, bypassed on special cases
    logic busy;
    logic new_request_r;
    assign issue.ready = ~busy | wb.ack;

    always_ff @(posedge clk) begin
        if (rst) begin
            busy <= 0;
            new_request_r <= 0;
        end
        else begin
            if (wb.ack)
                busy <= 0;
            if (issue.new_request)
                busy <= 1;
            new_request_r <= issue.new_request;
        end
    end

    ////////////////////////////////////////////////////
    //Special cases
    //Handle edge cases like negative numbers, infinity, NaN, zero, and powers of 2
    //Don't require mantissa calculation and bypass the core
    logic nv, nv_r;
    logic inf; //Default if not qnan_r or zero_r
    logic qnan, qnan_r;
    logic zero, zero_r;
    logic early_exit;
    logic result_sign;
    fp_t special_result;
    expo_d_t result_expo;

    assign nv = (args.rs1.d.sign & ~args.special_case.qnan & ~args.special_case.zero) | args.special_case.snan;
    assign qnan = args.special_case.qnan | nv;
    assign zero = args.special_case.zero;
    assign inf = args.special_case.inf & ~args.rs1.d.sign;

    always_ff @(posedge clk) begin
        if (rst)
            early_exit <= 0;
        else if (wb.ack)
            early_exit <= 0;
        else if (issue.new_request)
            early_exit <= inf | zero | qnan;
        
        if (issue.new_request) begin
            result_sign <= args.rs1.d.sign;
            nv_r <= nv;
            qnan_r <= qnan;
            zero_r <= zero;
        end
    end

    always_comb begin
        if (qnan_r)
            special_result.raw = CANONICAL_NAN;
        else if (zero_r) begin
            special_result.d.sign = result_sign;
            special_result.d.expo = '0;
            special_result.d.frac = '0;
        end
        else begin //Inf
            special_result.d.sign = 0;
            special_result.d.expo = '1;
            special_result.d.frac = '0;
        end
    end

    ////////////////////////////////////////////////////
    //Exponent logic
    //Normalized for subnormal inputs
    //Halved for positive exponents and doubled for negative exponents
    logic[EXPO_WIDTH:0] norm_expo;
    logic[EXPO_WIDTH:0] norm_expo_r;
    logic[EXPO_WIDTH:0] unbiased_expo;
    assign norm_expo = args.rs1.d.expo + {{(EXPO_WIDTH-1){1'b0}}, ~args.rs1_hidden} - args.rs1_prenormalize_shift_amt;

    assign unbiased_expo = norm_expo_r - {{(EXPO_WIDTH-1){1'b0}}, ~norm_expo_r[0]} - BIAS;
    //Right shift by 1 halves both positive and negative numbers
    assign result_expo = unbiased_expo[EXPO_WIDTH:1] + BIAS;

    always_ff @(posedge clk) begin
        if (issue.new_request)
            norm_expo_r <= norm_expo;
    end

    ////////////////////////////////////////////////////
    //Mantissa square root core
    //Designed to be swappable
    //Operates on normalized values shifted for alignment
    logic result_hidden;
    logic[3:0] result_grs;
    frac_d_t result_frac;
    assign sqrt.radicand = norm_expo[0] ? {2'b01, args.rs1.d.frac, 3'b0} : {1'b1, args.rs1.d.frac, 4'b0};
    assign sqrt.start = issue.new_request & ~(inf | zero | qnan);
    assign {result_hidden, result_frac, result_grs} = sqrt.result;

    fp_sqrt_core sqrt_core (
        .sqrt(sqrt),
    .*);

    ////////////////////////////////////////////////////
    //Output management
    //Either return the early execute values on cycle 1, or the regular values once the square root finishes
    logic sqrt_hold;
    assign wb.done = sqrt.done | sqrt_hold | early_exit;

    always_ff @(posedge clk) begin
        if (rst)
            sqrt_hold <= 0;
        else
            sqrt_hold <= ~wb.ack & (sqrt.done | sqrt_hold);
    end
    
    always_ff @(posedge clk) begin
        if (issue.new_request) begin
            wb.id <= issue.id;
            wb.rm <= args.rm;
            wb.d2s <= args.single;
        end
    end

    always_comb begin
        if (new_request_r)
            wb.rd = special_result;
        else begin
            wb.rd.d.sign = 0;
            wb.rd.d.expo = result_expo;
            wb.rd.d.frac = result_frac;
        end
        wb.grs = '0;
        if (~new_request_r) begin
            wb.grs[GRS_WIDTH-1-:4] = result_grs;
            wb.grs[GRS_WIDTH-5-:FRAC_WIDTH+5] = sqrt.remainder;
        end
    end
    assign wb.expo_overflow = 0;
    assign wb.fflags.nv = nv_r;
    assign wb.fflags.dz = 0;
    assign wb.fflags.of = 0;
    assign wb.fflags.uf = 0;
    assign wb.fflags.nx = 0; //Set in writeback
    assign wb.carry = 0;
    assign wb.safe = 0;
    assign wb.subnormal = 0;
    assign wb.hidden = (new_request_r & ~zero_r) | (~new_request_r & result_hidden);
    assign wb.clz = '0;
    assign wb.right_shift = 0;
    assign wb.right_shift_amt = 'x;
    assign wb.ignore_max_expo = 1;

endmodule
