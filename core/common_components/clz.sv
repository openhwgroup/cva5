/*
 * Copyright © 2023 Chris Keilbart, Lesley Shannon
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module clz

    #(
        parameter WIDTH = 32
    )
    (
        input logic[WIDTH-1:0] clz_input,
        output logic[$clog2(WIDTH)-1:0] clz,
        output logic zero
    );

    //Based on "Design of Leading Zero Counters on FPGAs" by Perri et al. 2022 (which is optimized for 6-input LUTs)

    //It is possible to unroll this and implement it without recursion
    //However, this significantly hurts readability especially with regards to the clz signal

    localparam TREE_WIDTH = 2**$clog2(WIDTH);
    localparam TREE_CLZ_WIDTH = $clog2(WIDTH)-1;
    localparam HALF_TREE_WIDTH = TREE_WIDTH/2;
    localparam WIDTH_DIFFERENCE = TREE_WIDTH - WIDTH;

    generate if (WIDTH == 2) begin : gen_base_case
            //Base case
            assign zero = ~(clz_input[1] | clz_input[0]);
            assign clz[0] = ~clz_input[1] & clz_input[0];
        end
        else begin : gen_recursive
            logic[TREE_WIDTH-1:0] padded_input;
            if (WIDTH_DIFFERENCE != 0) //Pad input on right if width is not a power of 2
                assign padded_input = {clz_input, {WIDTH_DIFFERENCE{1'b0}}};
            else
                assign padded_input = clz_input;
            logic[TREE_CLZ_WIDTH-1:0] upper_clz;
            logic[TREE_CLZ_WIDTH-1:0] lower_clz;
            logic upper_zero;
            logic lower_zero;
            assign zero = upper_zero & lower_zero;
            assign clz[$clog2(WIDTH)-1] = upper_zero;

            clz #(.WIDTH(HALF_TREE_WIDTH)) upper_tree (
                .clz_input(padded_input[TREE_WIDTH-1:HALF_TREE_WIDTH]),
                .clz(upper_clz),
                .zero(upper_zero)
            );
            clz #(.WIDTH(HALF_TREE_WIDTH)) lower_tree (
                .clz_input(padded_input[HALF_TREE_WIDTH-1:0]),
                .clz(lower_clz),
                .zero(lower_zero)
            );

            for (genvar i = 0; i < TREE_CLZ_WIDTH; i++) //Combine tree outputs
                assign clz[i] = (~upper_zero & upper_clz[i]) | (upper_zero & lower_clz[i]);
        end
    endgenerate

endmodule
