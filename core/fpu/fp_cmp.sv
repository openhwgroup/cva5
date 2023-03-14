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
 */

module fp_cmp
    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    import fpu_types::*;

(
    input logic clk,
    input logic advance,
    unit_issue_interface.unit issue,
    input fp_cmp_inputs_t fp_cmp_inputs,
    unit_writeback_interface.unit wb
);

    logic [2:0]             fn3;

    logic                   swap;
    logic                   rs1_sign;
    logic [EXPO_WIDTH-1:0]  rs1_expo;
    logic [FRAC_WIDTH-1:0]  rs1_frac;
    logic                   rs1_NaN;
    logic                   rs1_SNaN;
    logic                   rs1_zero;
    logic                   rs2_sign;
    logic [EXPO_WIDTH-1:0]  rs2_expo;
    logic [FRAC_WIDTH-1:0]  rs2_frac;
    logic                   rs2_NaN;
    logic                   rs2_SNaN;
    logic                   rs2_zero;
    logic                   invalid_cmp, r_invalid_cmp;
    logic                   unordered;
    logic                   flt, feq, fle;
    logic                   result, r_result;
    logic                   done;
    id_t                    id;

    ////////////////////////////////////////////////////
    //Implementation
    //unpack
    assign rs1_NaN = |fp_cmp_inputs.rs1_special_case[2:1];
    assign rs2_NaN = |fp_cmp_inputs.rs2_special_case[2:1];
    assign rs1_SNaN = fp_cmp_inputs.rs1_special_case[2];
    assign rs2_SNaN = fp_cmp_inputs.rs2_special_case[2];
    assign rs1_zero = fp_cmp_inputs.rs1_special_case[0];
    assign rs2_zero = fp_cmp_inputs.rs2_special_case[0];
    assign fn3 = fp_cmp_inputs.rm;
    assign swap = fp_cmp_inputs.swap;

    assign rs1_sign = fp_cmp_inputs.rs1[FLEN-1];
    assign rs2_sign = fp_cmp_inputs.rs2[FLEN-1];
    assign rs1_expo = fp_cmp_inputs.rs1[FLEN-2-:EXPO_WIDTH];
    assign rs2_expo = fp_cmp_inputs.rs2[FLEN-2-:EXPO_WIDTH];
    assign rs1_frac = fp_cmp_inputs.rs1[0+:FRAC_WIDTH];
    assign rs2_frac = fp_cmp_inputs.rs2[0+:FRAC_WIDTH];

    //special case handling

    assign invalid_cmp = ((fn3 != 3'b010) & (rs1_NaN | rs2_NaN)) |  // FLT FLE signaling comparison
                        ((fn3 == 3'b010) & (rs1_SNaN | rs2_SNaN)); // FEQ quiet comparison
    assign unordered = rs1_NaN | rs2_NaN;

    //FEQ
    logic sign_equ, expo_equ, frac_equ;

    assign sign_equ = ~(rs1_sign ^ rs2_sign);
    assign expo_equ = ~|(rs1_expo ^ rs2_expo);
    assign frac_equ = ~|(rs1_frac ^ rs2_frac);

    assign feq = (rs1_zero & rs2_zero) | (sign_equ & expo_equ & frac_equ);

    ////////////////////////////////////////////////////
    //FLT
    always_comb begin
        if (sign_equ)
            flt = (swap ^ rs1_sign) & ~feq;
        else
            flt = rs1_sign & ~(rs1_zero & rs2_zero);
    end

    ////////////////////////////////////////////////////
    //FLE
    assign fle = flt || feq;

    ////////////////////////////////////////////////////
    //Register
    always_ff @ (posedge clk) begin //TODO is this needed?
        if (advance) begin
            done <= issue.new_request;
            id <= issue.id;
            r_result <= result;
            r_invalid_cmp <= invalid_cmp;
        end
    end

    ////////////////////////////////////////////////////
    //Output
    always_comb begin
        case(fn3)
        default: begin
            result = fle & ~unordered;
        end
        3'b001: begin
            result = flt & ~unordered;
        end
        3'b010: begin
            result = feq & ~unordered;
        end
        endcase
    end

    assign wb.rd = XLEN'(r_result);
    assign wb.done = done;
    assign wb.id = id;
    assign wb.fflags = {r_invalid_cmp, 4'b0};

endmodule
