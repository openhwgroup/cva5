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

module fp_sqrt_core

    (
        input logic clk,
        input logic rst,
        unsigned_sqrt_interface.sqrt sqrt
    );

    typedef logic[$clog2(sqrt.DATA_WIDTH)-1:0] counter_t;
    typedef logic[sqrt.DATA_WIDTH-1:0] frac_t;

    ////////////////////////////////////////////////////
    //Radix 2 square root
    //Fixed latency generating one result bit per cycle

    //Control logic
    logic counter_full;
    counter_t counter;
    assign counter_full = counter == counter_t'(sqrt.DATA_WIDTH);

    always_ff @(posedge clk) begin
        if (rst) begin
            counter <= '0;
            sqrt.done <= 0;
        end
        else begin
            sqrt.done <= counter_full;
            if (counter_full)
                counter <= '0;
            else if (sqrt.start | |counter)
                counter <= counter + 1;
        end
    end

    ////////////////////////////////////////////////////
    //Subtraction
    frac_t rad;
    frac_t current_subtractend;
    frac_t next_subtractend;
    frac_t subtractor;
    frac_t subtraction;
    logic overflow;

    assign subtractor = {sqrt.result[sqrt.DATA_WIDTH-3:0], 2'b01};
    assign {overflow, subtraction} = current_subtractend - subtractor;

    ////////////////////////////////////////////////////
    //Next Working subtractend Determination
    always_comb begin
        if (overflow)
            next_subtractend = {current_subtractend[sqrt.DATA_WIDTH-3:0], rad[sqrt.DATA_WIDTH-1-:2]};
        else
            next_subtractend = {subtraction[sqrt.DATA_WIDTH-3:0], rad[sqrt.DATA_WIDTH-1-:2]};
    end

    always_ff @(posedge clk) begin
        if (sqrt.start) //First working subtractend extracts the upper 2 bits of the radicand
            current_subtractend <= {{(sqrt.DATA_WIDTH-2){1'b0}}, sqrt.radicand[sqrt.DATA_WIDTH-1-:2]};
        else
            current_subtractend <= next_subtractend;
    end

    ////////////////////////////////////////////////////
    //Update remaining radicand digits
    always_ff @(posedge clk) begin
        if (sqrt.start) //The upper two bits are pushed to the working subtractend register
            rad <= {sqrt.radicand[sqrt.DATA_WIDTH-3:0], 2'b00};
        else
            rad <= rad << 2;
    end

    ////////////////////////////////////////////////////
    //Quotient Determination
    always_ff @(posedge clk) begin
        if (sqrt.start) begin
            sqrt.result <= '0;
            sqrt.remainder <= '0;
        end
        else if (|counter) begin
            //Shift in new quotient bit
            sqrt.result <= {sqrt.result[sqrt.DATA_WIDTH-2:0], ~overflow};
            sqrt.remainder <= next_subtractend;
        end
    end

endmodule
