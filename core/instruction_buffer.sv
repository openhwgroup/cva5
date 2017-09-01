/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 * 
 * This Source Code Form is "Incompatible With Secondary Licenses", as
 * defined by the Mozilla Public License, v. 2.0.
 *
 * Initial code developed under the supervision of Dr. Lesley Shannon,
 * Reconfigurable Computing Lab, Simon Fraser University.
 *
 * Author(s):
 *             Eric Matthews <ematthew@sfu.ca>
 */
 
import taiga_config::*;
import taiga_types::*;

//Circular buffer for instruction buffer.  Isolates push and pop signals so that critical paths can be separated
module instruction_buffer
        (
        input logic clk,
        input logic rst,
        instruction_buffer_interface.buffer ib
        );

    logic[$bits(instruction_buffer_packet)-1:0] shift_reg[FETCH_BUFFER_DEPTH-1:0];
    logic[$bits(instruction_buffer_packet)-1:0] shift_reg_in;
    instruction_buffer_packet shift_reg_out;


    logic [$clog2(FETCH_BUFFER_DEPTH)-1:0] write_index;
    logic [$clog2(FETCH_BUFFER_DEPTH)-1:0] read_index;

    logic count_v [FETCH_BUFFER_DEPTH:0];


    //implementation
    always_ff @ (posedge clk) begin
        if (rst | ib.flush) begin
            write_index <= 0;
            read_index <= 0;
        end
        else begin
            read_index <= read_index + ib.pop;
            write_index <= write_index + ib.push;
        end
    end

    assign ib.early_full = count_v[FETCH_BUFFER_DEPTH-1] | count_v[FETCH_BUFFER_DEPTH];
    assign ib.full = count_v[FETCH_BUFFER_DEPTH];
    assign ib.valid = ~count_v[0];

    always_ff @ (posedge clk) begin
        if (rst | ib.flush) begin
            count_v[0] <= 1;
            for (int i = 1; i <= FETCH_BUFFER_DEPTH; i++) count_v[i] <= 0;
        end
        else if (ib.push & ~ib.pop)
            count_v <= {count_v[FETCH_BUFFER_DEPTH-1:0], 1'b0};
        else if (~ib.push & ib.pop)
            count_v <= {1'b0, count_v[FETCH_BUFFER_DEPTH:1]};
    end

    always_ff @ (posedge clk) begin
        if (ib.push)
            shift_reg[write_index] <=  ib.data_in;
    end

    assign ib.data_out = shift_reg[read_index];

endmodule


