/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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

    logic [DATA_WIDTH-1:0] lut_ram[FIFO_DEPTH-1:0];

    logic[$clog2(FIFO_DEPTH)-1:0] read_index;
    logic[$clog2(FIFO_DEPTH)-1:0] read_index_new;
    logic[$clog2(FIFO_DEPTH)-1:0] write_index;
    logic[$clog2(FIFO_DEPTH)-1:0] write_index_new;

    logic two_plus;
    ////////////////////////////////////////////////////////
    //implementation

    assign fifo.data_out = lut_ram[read_index];

    assign read_index_new = read_index + fifo.pop;
    assign write_index_new = write_index + fifo.push;

    always_ff @ (posedge clk) begin
        if (rst) begin
            read_index <= 0;
            write_index <= 0;
        end
        else begin
            read_index <= read_index_new;
            write_index <= write_index_new;
        end
    end


    always_ff @ (posedge clk) begin
        if (rst | (fifo.pop & ~fifo.push & ~fifo.full))
            fifo.early_full <= 0;
        else if (fifo.push & ~fifo.pop)
            fifo.early_full <= (write_index+2 == read_index);
    end

    always_ff @ (posedge clk) begin
        if (rst | (fifo.pop & ~fifo.push))
            fifo.full <= 0;
        else if (fifo.push & ~fifo.pop)
            fifo.full <= (write_index_new == read_index);
    end

    always_ff @ (posedge clk) begin
        if (rst | (fifo.pop & ~fifo.push && (read_index_new == write_index)))
            fifo.valid <= 0;
        else if (fifo.push)
            fifo.valid <= 1;
    end

    always_ff @ (posedge clk) begin
        if (rst | (fifo.pop & ~fifo.push && (read_index+2 == write_index)))
            two_plus <= 0;
        else if (fifo.valid & fifo.push & ~fifo.pop)
            two_plus <= 1;
    end

    always_ff @ (posedge clk) begin
        if (fifo.push)
            lut_ram[write_index] <= fifo.data_in;
    end


    //pushing, or more than one, or at least one and not popping
    assign fifo.early_valid = fifo.push | (two_plus) | (fifo.valid & ~fifo.pop);

endmodule


