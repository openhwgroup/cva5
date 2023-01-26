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

module sticky_generator_onehot
#(
    parameter INPUT_WIDTH = 53,
    parameter SHIFT_WIDTH = 6
)(
    input logic [INPUT_WIDTH-1:0] d_in,
    input logic [SHIFT_WIDTH-1:0] shft_amt,
    output logic sticky
);

    localparam INPUT_WIDTH_WITHOUT_HIDDEN_BIT = INPUT_WIDTH - 1;
    logic one_hot_in;
    localparam PADDED_WIDTH = INPUT_WIDTH+3;
    logic [INPUT_WIDTH-1:0] shft_amt_one_hot;
    logic [INPUT_WIDTH-1:0] d_in_reversed;
    logic [INPUT_WIDTH-1:0] sticky_bit_mask;
    logic [INPUT_WIDTH-1:0] sticky_bit_mask_reversed;
    logic [INPUT_WIDTH-1:0] shft_amt_one_hot_debug;
    logic [INPUT_WIDTH-1:0] sum;

    always_comb begin
        one_hot_in = |shft_amt[5:2] | &shft_amt[1:0];
        shft_amt_one_hot = 0;
        shft_amt_one_hot[shft_amt-2] = one_hot_in;
        shft_amt_one_hot_debug = 0;
        shft_amt_one_hot_debug[INPUT_WIDTH-shft_amt+2] = one_hot_in;
        sticky_bit_mask = (shft_amt_one_hot - INPUT_WIDTH'(one_hot_in)); //subtractor

        // reverse two operands
        for (int i = 0; i < INPUT_WIDTH; i++) begin
            d_in_reversed[i] = d_in[INPUT_WIDTH-1-i];
            sticky_bit_mask_reversed[i] = sticky_bit_mask[INPUT_WIDTH-1-i];
        end
    end

    assign {sticky, sum} = d_in_reversed + sticky_bit_mask_reversed;
endmodule

module sticky_bit_onehot
#(
    parameter INPUT_WIDTH = 24
)(
    input logic [INPUT_WIDTH - 1 : 0] shifter_input,
    input logic [$clog2(INPUT_WIDTH)-1:0] shift_amount,
    output logic sticky_bit
);

    //Padded with +3 as per stickybit definition (OR of bits shifted out by at least 3 bits)
    localparam PADDED_WIDTH = INPUT_WIDTH + 3;

    logic one_hot_in;
    logic [PADDED_WIDTH - 1 : 0] padded_input;
    logic [INPUT_WIDTH - 1 : 0] one_hot_shift;
    (* keep = "true" *) logic [PADDED_WIDTH - 1 : 0] padded_one_hot_shift;
    logic [PADDED_WIDTH:0] adder_in1, adder_in2;
    logic [PADDED_WIDTH - 1 : 0] sum;
    logic carry_in;
    always_comb begin
        padded_input = '{default: '0};
        padded_input[3 +: INPUT_WIDTH] = shifter_input;

        one_hot_shift = '0;
        one_hot_shift[shift_amount-1] = 1;

        padded_one_hot_shift = '0;
        for (int i = 0; i < INPUT_WIDTH; i++) begin
            padded_one_hot_shift[i+3] = one_hot_shift[INPUT_WIDTH-1-i];
        end

        adder_in1 = {({PADDED_WIDTH{1'b1}} ^ padded_one_hot_shift), 1'b1};
        adder_in2 = {padded_input, 1'b1};

        {sticky_bit, sum, carry_in} = {({PADDED_WIDTH{1'b1}} ^ padded_one_hot_shift), 1'b1} + {padded_input, 1'b1};
    end
endmodule

module sticky_bit_logic
#(
    parameter INPUT_WIDTH = 24
)
(
    input logic [INPUT_WIDTH - 1 : 0] shifter_input,
    input logic [$clog2(INPUT_WIDTH)-1:0] shift_amount,
    output logic sticky_bit
);

    //ORs all shifted
    function logic shift_reduce  (input logic [3:0] a, logic [1:0] sel, logic fully_shifted);
        case({fully_shifted, sel})
            0 : shift_reduce = a[0];
            1 : shift_reduce = |a[1:0];
            2 : shift_reduce = |a[2:0];
            default : shift_reduce = |a;
        endcase
    endfunction

    //Padded with +3 as per stickybit definition (OR of bits shifted out by at least 3 bits)
    localparam PADDED_WIDTH = INPUT_WIDTH + 3; //56

    //Padd with 3 bits to only capture bits from shifts that are larger than 3
    localparam NUM_TIERS = ($clog2(PADDED_WIDTH)+1)/2;//clog4

    //All tiers sized to largerst (lowest) tier size, unused inputs will be tied to zero
    //+3 to ensure enough zero padding for grouping into sets of four
    logic [PADDED_WIDTH + 3 - 1 : 0] tier [NUM_TIERS];

    ////////////////////////////////////////////////////
    //Implementation
    int TIER_WIDTH;
    int curr_shift_amount;
    always_comb begin
        tier = '{default: '0};
        tier[0][3 +: INPUT_WIDTH] = shifter_input;

        TIER_WIDTH = (PADDED_WIDTH+2)/4; //+2 --> round up to nearest multiple of four // 14
        for (int i = 1; i < NUM_TIERS; i++) begin
            curr_shift_amount = 32'(shift_amount) >> 2*i;
            for (int j = 0; j < TIER_WIDTH; j++) begin
                tier[i][j] = shift_reduce(tier[i-1][j*4 +: 4], shift_amount[(i-1)*2 +: 2], j < curr_shift_amount);//(32'(shift_amount) >> (2*i)));
            end
            TIER_WIDTH = (TIER_WIDTH+2)/4;
        end

        sticky_bit = shift_reduce(tier[NUM_TIERS-1][3:0], shift_amount[$clog2(INPUT_WIDTH)-1 -: 2], 1'b0);
    end
endmodule
