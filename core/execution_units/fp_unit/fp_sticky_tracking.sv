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

module fp_sticky_tracking

    #(
        parameter INPUT_WIDTH = 24,
        parameter SHIFT_WIDTH = 11
    )(
        input logic[INPUT_WIDTH-1:0] shifter_input,
        input logic[SHIFT_WIDTH-1:0] shift_amount,
        output logic sticky_bit
    );
    
    //This unit returns a single bit which indicates whether a 1 got right shifted out of the input

    //ORs all shifted
    function logic shift_reduce(input logic[3:0] a, input logic[1:0] sel, input logic fully_shifted);
        case({fully_shifted, sel})
            0 : shift_reduce = a[0];
            1 : shift_reduce = |a[1:0];
            2 : shift_reduce = |a[2:0];
            default : shift_reduce = |a;
        endcase
    endfunction

    localparam PADDED_WIDTH = 2**SHIFT_WIDTH;
    localparam NUM_TIERS = (SHIFT_WIDTH+1)/2; //log4 - each level reduces width by a factor of 4
    logic[PADDED_WIDTH-1:0] tier[NUM_TIERS];

    ////////////////////////////////////////////////////
    //Implementation
    int tier_width;
    int curr_shift_amount;
    always_comb begin
        tier = '{default: '0};
        //Pad with 0s to ensure that shift amounts larger than INPUT_WIDTH generate the correct sticky
        tier[0] = {{(PADDED_WIDTH-INPUT_WIDTH){1'b0}}, shifter_input};

        tier_width = PADDED_WIDTH/4;
        for (int i = 1; i < NUM_TIERS; i++) begin
            curr_shift_amount = 32'(shift_amount) >> 2*i;
            for (int j = 0; j < tier_width; j++)
                tier[i][j] = shift_reduce(tier[i-1][j*4 +: 4], shift_amount[(i-1)*2 +: 2], j < curr_shift_amount);
            tier_width = tier_width/4;
        end

        sticky_bit = shift_reduce(tier[NUM_TIERS-1][3:0], shift_amount[$clog2(PADDED_WIDTH)-1 -: 2], 1'b0);
    end
endmodule
