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

/*
 *  LUT RAM FIFO implementation.  Not underflow/overflow safe.
 *  Intended for small FIFO depths.
 */
module lutram_fifo #(parameter DATA_WIDTH = 42, parameter FIFO_DEPTH = 4)
        (
        input logic clk,
        input logic rst,
        fifo_interface.structure fifo
        );

    logic[DATA_WIDTH-1:0] lut_ram[FIFO_DEPTH-1:0];

    logic[$clog2(FIFO_DEPTH)-1:0] write_index;
    logic[$clog2(FIFO_DEPTH)-1:0] read_index;

    logic count_v [FIFO_DEPTH:0];
    ////////////////////////////////////////////////////////
    //implementation

    assign fifo.data_out = lut_ram[read_index];

    always_ff @ (posedge clk) begin
        if (rst) begin
            read_index <= '0;
            write_index <= '0;
        end
        else begin
            read_index <= read_index + fifo.pop;
            write_index <= write_index + fifo.push;
        end
    end

    assign fifo.early_full = count_v[FIFO_DEPTH-1] | count_v[FIFO_DEPTH];
    assign fifo.full = count_v[FIFO_DEPTH];
    assign fifo.valid = ~count_v[0];

    always_ff @ (posedge clk) begin
        if (fifo.push)
            lut_ram[write_index] <= fifo.data_in;
    end

    //set bit indicates occupancy, index zero is empty.
    always_ff @ (posedge clk) begin
        if (rst) begin
            count_v[0] <= 1;
            for (int i = 1; i <= FIFO_DEPTH; i++) count_v[i] <= 0;
        end
        else if (fifo.push & ~fifo.pop)
            count_v <= {count_v[FIFO_DEPTH-1:0], 1'b0};
        else if (~fifo.push & fifo.pop)
            count_v <= {1'b0, count_v[FIFO_DEPTH:1]};
    end

    //pushing, or more than one, or at least one and not popping
    assign fifo.early_valid = fifo.push | (~count_v[0] & ~count_v[1]) | (~count_v[0] & ~fifo.pop);

endmodule


