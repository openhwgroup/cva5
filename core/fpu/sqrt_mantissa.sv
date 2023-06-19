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


module sqrt_mantissa
    import taiga_config::*;
#(
    ITERATION = 50
)(
    input logic clk,
    input logic rst,
    unsigned_sqrt_interface.sqrt sqrt
);

    logic running;
    logic terminate;
    int counter;

    localparam CLZ_W = $clog2(sqrt.DATA_WIDTH);
    int active_data_width;

    ////////////////////////////////////////////////////
    //Control Signals
    assign active_data_width = sqrt.DATA_WIDTH - (32'(radicand_clz) - 32'(odd));

    always_ff @ (posedge clk) begin
        if (rst)
            running <= 0;
        else if (sqrt.start)
            running <= 1;
        else if (terminate)
            running <= 0;
    end

    always_ff @ (posedge clk) begin
        sqrt.done <= (running & terminate);
        if (rst)
            counter <= 0;
        else if (sqrt.start)
            counter <= 1;
        else if (running & ~terminate)
            counter <= counter + 1;
    end

    //assign sqrt.done = terminate & running;
    assign terminate = counter > ITERATION | sqrt.early_terminate;;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Normalize radicand
    logic [CLZ_W-1:0] radicand_clz;
    logic odd;
    int i;
    logic [sqrt.DATA_WIDTH-1:0] normalized_radicand;
    //clz clz_radicand (.clz_input(sqrt.radicand), .clz(radicand_clz));
    always_comb begin
        for (i = 0; i < FRAC_WIDTH; i++) begin
            if (sqrt.radicand[sqrt.DATA_WIDTH-1-i] == 1) begin
                break;
            end
        end
        radicand_clz = i[CLZ_W-1:0];
    end

    assign odd = radicand_clz[0];
    assign normalized_radicand = sqrt.radicand << (radicand_clz - CLZ_W'(odd));

    ////////////////////////////////////////////////////
    //Subtraction
    logic [sqrt.DATA_WIDTH-1:0] rad, next_rad;
    logic [sqrt.DATA_WIDTH-1:0] current_subtractend, next_subtractend;
    logic [sqrt.DATA_WIDTH-1:0] subtractor, subtraction;

    assign subtractor = (sqrt.DATA_WIDTH)'({sqrt.quotient[sqrt.DATA_WIDTH-3:0], 2'b01});
    assign subtraction = current_subtractend - subtractor;

    ////////////////////////////////////////////////////
    //Next Working subtractend Determination
    logic overflow;
    assign overflow = subtraction[sqrt.DATA_WIDTH-1];
    always_comb begin
        if (overflow)
            next_subtractend = {current_subtractend[sqrt.DATA_WIDTH-3:0], rad[sqrt.DATA_WIDTH-1-:2]};
        else
            next_subtractend = {subtraction[sqrt.DATA_WIDTH-3:0], rad[sqrt.DATA_WIDTH-1-:2]};
    end

    always_ff @ (posedge clk) begin
        if (sqrt.start)
            //first working subtractend if the upper 2 bits of the radicand
            current_subtractend <= sqrt.DATA_WIDTH'(normalized_radicand[sqrt.DATA_WIDTH-1-:2]);
        else if(~terminate & running)
            current_subtractend <= next_subtractend;
    end

    ////////////////////////////////////////////////////
    //Update remaining radicand digits
    //TODO: can optimize to just shift left on posedge clk
    assign next_rad = {rad[sqrt.DATA_WIDTH-3:0], 2'b0};

    always_ff @ (posedge clk) begin
        if (sqrt.start)
            //the upper two bits are pushed to the working subtractend register
            rad <= {normalized_radicand[sqrt.DATA_WIDTH-3:0], 2'b00};
        else if(~terminate & running)
            rad <= next_rad;
    end

    ////////////////////////////////////////////////////
    //Quotient Determination
    logic [sqrt.DATA_WIDTH-1:0] new_Q;
    logic new_Q_bit;

    assign new_Q_bit = ~overflow;
    assign new_Q = {sqrt.quotient[0+:sqrt.DATA_WIDTH-1], new_Q_bit};

    always_ff @ (posedge clk) begin
        if (sqrt.start) begin
            sqrt.quotient <= '0;
            sqrt.remainder <= '0;
        end else if (~terminate & running) begin
            sqrt.quotient <= sqrt.DATA_WIDTH'(new_Q);
            sqrt.remainder <= next_subtractend;
        end
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

endmodule
