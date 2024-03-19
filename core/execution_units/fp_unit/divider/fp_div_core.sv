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

module fp_div_core

    import fpu_types::*;

    (
        input logic clk,
        input logic rst,
        unsigned_division_interface.divider div
    );

    localparam DIV_WIDTH = div.DATA_WIDTH;
    localparam COUNTER_WIDTH = $clog2((1+DIV_WIDTH)/2+3);
    localparam QUOTIENT_WIDTH = 2*((1+DIV_WIDTH)/2)+2;
    localparam DECIMAL_WIDTH = DIV_WIDTH+1;
    localparam RESIDUE_WIDTH = DIV_WIDTH+3;

    ////////////////////////////////////////////////////
    //Radix 4 divider
    //Follows the design in "Digital Arithmetic" by Ercegovac and Lang
    //Uses the digit set {-2, -1, 0, 1, 2}
    logic[RESIDUE_WIDTH-1:0] four_wsum; //Shifted left twice
    logic[DECIMAL_WIDTH-1:0] wcarry;
    logic[DECIMAL_WIDTH-2:0] divisor_r;
    logic[DECIMAL_WIDTH-1:0] next_wsum;
    logic[DECIMAL_WIDTH-1:0] next_wcarry;

    q_t current_q;
    q_t next_q;
    q_t muxed_q;

    logic[QUOTIENT_WIDTH-1:0] quotient;
    logic[QUOTIENT_WIDTH-1:0] quotient_m;
    logic[QUOTIENT_WIDTH-1:0] next_quotient;
    logic[QUOTIENT_WIDTH-1:0] next_quotient_m;

    //Assertions
    logic decremented_invalid;
    logic bad_quotient_digit;
    logic not_in_table;

    //Control logic
    logic [COUNTER_WIDTH-1:0] counter;
    logic counter_full;
    assign counter_full = counter == COUNTER_WIDTH'((1+DIV_WIDTH)/2+2);

    always_ff @(posedge clk) begin
        if (rst) begin
            counter <= '0;
            div.done <= 0;
        end
        else begin
            div.done <= counter_full;
            if (counter_full)
                counter <= '0;
            else if (div.start | |counter)
                counter <= counter + 1;
        end
    end

    //Iterate over the digits
    always_ff @(posedge clk) begin
        if (rst) begin
            divisor_r <= '0;
            four_wsum <= '0;
            wcarry <= '0;
            quotient <= '0;
            quotient_m <= '0;
            current_q <= ZERO;
        end
        else begin
            if (div.start) begin
                divisor_r <= div.divisor;
                four_wsum <= {3'b0, div.dividend}; //First iteration doesn't shift the inputs
                current_q <= ZERO;
                wcarry <= '0;
                quotient <= '0;
                quotient_m <= '0;
            end
            else if (|counter) begin
                current_q <= next_q;
                four_wsum <= {next_wsum, 2'b0};
                wcarry <= next_wcarry;
                quotient <= next_quotient;
                quotient_m <= next_quotient_m;
            end
        end
    end
    assign div.quotient = quotient[QUOTIENT_WIDTH-2 -: DIV_WIDTH]; //Shift only once instead of twice because inputs are in the range 0.1X but the output can be X.XX


    //Carry save adder operating on shifted input
    carry_save_shift #(.WIDTH(RESIDUE_WIDTH)) partial_sum (
        .four_wsum(four_wsum),
        .wcarry(wcarry),
        .divisor(divisor_r),
        .next_wsum(next_wsum),
        .next_wcarry(next_wcarry),
        .next_q(next_q),
        .not_in_table(not_in_table)
    );

    //Digit conversion
    on_the_fly #(.WIDTH(QUOTIENT_WIDTH)) quotient_conv (
        .current_Q(quotient),
        .current_QM(quotient_m),
        .q(muxed_q),
        .next_Q(next_quotient),
        .next_QM(next_quotient_m),
        .bad_quotient_digit(bad_quotient_digit)
    );

    ////////////////////////////////////////////////////
    //Sign/zero detection using an adder
    //The alternative is a tree of generate/propagate blocks (see page 265 of "Digital Arithmetic" by Ercegovac and Lang)
    //For a 55 bit width, both have very similar delays but the tree uses slightly more resources
    logic is_negative;
    logic[DECIMAL_WIDTH-1:0] sz_sum;
    assign sz_sum = four_wsum[RESIDUE_WIDTH-1:2] + wcarry;
    assign is_negative = sz_sum[DECIMAL_WIDTH-1];

    always_comb begin
        div.remainder = sz_sum[DIV_WIDTH-1:0]; 

        muxed_q = current_q;
        decremented_invalid = 0;
        if (counter_full & is_negative) begin //Subtract 1
            unique case (current_q)
                POS_TWO: muxed_q = POS_ONE;
                POS_ONE: muxed_q = ZERO;
                ZERO: muxed_q = NEG_ONE;
                NEG_ONE: muxed_q = NEG_TWO;
                NEG_TWO: muxed_q = NEG_THREE;
                default: decremented_invalid = 1; //For assertions only
            endcase
        end
    end


    //Assertions
    decrement_bad_quotient_assertion:
        assert property (@(posedge clk) disable iff (rst) (!(decremented_invalid)))
        else $error("Invalid decrement of quotient digit");

    decoding_bad_digit_assertion:
        assert property (@(posedge clk) disable iff (rst) (!(|counter & bad_quotient_digit)))
        else $error("Bad quotient digit for decoding");

    missed_lut_assertion:
        assert property (@(posedge clk) disable iff (rst) (!(|counter & not_in_table)))
        else $error("Sum out of range of quotient lookup");

endmodule
