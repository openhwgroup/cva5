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

module fp_round_simplified
    import taiga_config::*;

(
    input logic                   sign,
    input logic [2:0]             rm,
    input logic [2:0]             grs,
    input logic                   lsb,
    output logic                  roundup,
    output logic [FLEN-1:0]       result_if_overflow
);
    //ties to even 000
    //round toward zero 001
    //round toward negatve 010
    //round  toward positive 011
    //ties to max magnitutude 100

    generate if (FULL_ROUNDING_MODES_ENABLE) begin
        always_comb begin
            case(rm)
                default: begin  //nearest ties to even
                    result_if_overflow = {sign, {EXPO_WIDTH{1'b1}}, {FRAC_WIDTH{1'b0}}};
                    roundup = grs[2] & lsb | (grs[2] & |grs[1:0]);
                end
                3'b100: begin  //nearest ties to away
                    result_if_overflow = {sign, {EXPO_WIDTH{1'b1}}, {FRAC_WIDTH{1'b0}}};
                    roundup = grs[2];
                end
                3'b011: begin //round to positive inf
                    //only round if: positive, has extra bits in grs
                    result_if_overflow = {sign, {(EXPO_WIDTH-1){1'b1}}, !sign, {FRAC_WIDTH{sign}}};
                    roundup = ~sign & |grs;
                end
                3'b010: begin  //round to negative inf
                    //only round if: negative, has extra bits in grs
                    result_if_overflow = {sign, {(EXPO_WIDTH-1){1'b1}}, sign, {FRAC_WIDTH{!sign}}};
                    roundup = sign & |grs;
                end
                3'b001: begin //round to zero
                    result_if_overflow = {sign, {(EXPO_WIDTH-1){1'b1}}, 1'b0, {FRAC_WIDTH{1'b1}}};
                    roundup = 0;
                end
            endcase
        end
    end else begin
        always_comb begin
            if(rm == 3'b000) begin
                result_if_overflow = {sign, {EXPO_WIDTH{1'b1}}, {FRAC_WIDTH{1'b0}}};
                roundup = grs[2] & lsb | (grs[2] & |grs[1:0]);
            end else begin
                result_if_overflow = 0;//{sign, {EXPO_WIDTH{1'b1}}, {FRAC_WIDTH{1'b0}}};
                roundup = 0;//grs[2] & lsb | (grs[2] & |grs[1:0]);
            end
        end
    end endgenerate
endmodule
