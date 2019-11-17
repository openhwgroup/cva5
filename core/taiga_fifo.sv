/*
 * Copyright © 2017-2019 Eric Matthews,  Lesley Shannon
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
 *  FIFOs Not underflow/overflow safe.
 *  Intended for small FIFO depths.
 *  For continuous operation when full, enqueing side must inspect pop signal
 */
module taiga_fifo #(parameter DATA_WIDTH = 70, parameter FIFO_DEPTH = 4)
        (
        input logic clk,
        input logic rst,
        fifo_interface.structure fifo
        );

    localparam LOG2_FIFO_DEPTH = $clog2(FIFO_DEPTH);
    //Force FIFO depth to next power of 2
    (* ramstyle = "MLAB, no_rw_check" *) logic[DATA_WIDTH-1:0] lut_ram[(2**LOG2_FIFO_DEPTH)-1:0];
    logic [LOG2_FIFO_DEPTH-1:0] write_index;
    logic [LOG2_FIFO_DEPTH-1:0] read_index;
    logic [LOG2_FIFO_DEPTH:0] inflight_count;
    logic supressed_push;

    ////////////////////////////////////////////////////
    //Implementation
    assign supressed_push = fifo.push & ~fifo.supress_push;
    generate if (FIFO_DEPTH == 1) begin
        always_ff @ (posedge clk) begin
            if (rst)
                fifo.valid <= 0;
            else if (supressed_push)
                fifo.valid <= 1;
            else if (fifo.pop)
                fifo.valid <= 0;
        end
        assign fifo.full = fifo.valid;

        always_ff @ (posedge clk) begin
            if (fifo.push)
                fifo.data_out <= fifo.data_in;
        end
    end
    else begin
        ////////////////////////////////////////////////////
        //Occupancy Tracking
        always_ff @ (posedge clk) begin
            if (rst)
                inflight_count <= 0;
            else
                inflight_count <= inflight_count + (LOG2_FIFO_DEPTH+1)'(fifo.pop) - (LOG2_FIFO_DEPTH+1)'(supressed_push);
        end

        assign fifo.valid = inflight_count[LOG2_FIFO_DEPTH];
        assign fifo.full = fifo.valid & ~|inflight_count[LOG2_FIFO_DEPTH-1:0];

        always_ff @ (posedge clk) begin
            if (rst) begin
                read_index <= '0;
                write_index <= '0;
            end
            else begin
                read_index <= read_index + LOG2_FIFO_DEPTH'(fifo.pop);
                write_index <= write_index + LOG2_FIFO_DEPTH'(supressed_push);
            end
        end

        always_ff @ (posedge clk) begin
            if (fifo.push)
                lut_ram[write_index] <= fifo.data_in;
        end
        assign fifo.data_out = lut_ram[read_index];
    end
    endgenerate

    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert (!(~rst & fifo.full & supressed_push & ~fifo.pop)) else $error("overflow");
        //assert (!(~rst & ~fifo.valid & ~supressed_push & fifo.pop)) else $error("underflow");
    end
endmodule


