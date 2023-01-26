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

module pre_normalize
import taiga_config::*;

#(
  parameter WIDTH=FRAC_WIDTH+1
)(
    input logic [FLEN-1:0] rs2,
    input logic rs2_hidden_bit,
    input logic enable,
    output logic [EXPO_WIDTH-1:0] pre_normalize_shift_amt,
    output logic [WIDTH-1:0] frac_normalized
);

    logic [WIDTH-1:0] frac;
    logic [EXPO_WIDTH-1:0] clz_with_prepended_0s;

    ////////////////////////////////////////////////////
    //Implementation
    //Unpack
    assign frac = {{(WIDTH-(FRAC_WIDTH+1)){1'b0}}, rs2_hidden_bit, rs2[FRAC_WIDTH-1:0]};

    //CLZ on subnormal input, and left shift to normalize
    //Assuming clz instances are optimized away when ENABLE_SUBNORMAL == 0
    generate if (FRAC_WIDTH+1 <= 32) begin
        localparam CLZ_OFFSET = (32 - (FRAC_WIDTH + 1));
        clz frac_clz (
            .clz_input (32'(frac)),
            .clz (clz_with_prepended_0s[4:0])
        );
        assign pre_normalize_shift_amt = clz_with_prepended_0s & {EXPO_WIDTH{enable}} - (CLZ_OFFSET & {EXPO_WIDTH{enable}});
    end else begin
        localparam CLZ_OFFSET = (64 - (FRAC_WIDTH + 1));
        clz_tree frac_clz (
            .clz_input (64'(frac)),
            .clz (clz_with_prepended_0s[5:0])
        );
        assign pre_normalize_shift_amt = (clz_with_prepended_0s & {EXPO_WIDTH{enable}}) - (CLZ_OFFSET & {EXPO_WIDTH{enable}});
    end endgenerate

    generate if (ENABLE_SUBNORMAL) begin
        assign frac_normalized = frac << pre_normalize_shift_amt;
    end else begin
        assign frac_normalized = frac;
    end
    endgenerate

    function logic [EXPO_WIDTH-1:0] getMin(input logic [EXPO_WIDTH-1:0] x, y);
        getMin = x > y ? y : x;
    endfunction

endmodule
