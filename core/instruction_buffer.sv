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

//Circular buffer for instruction buffer.  Isolates push and pop signals so that critical paths can be separated
module instruction_buffer
        (
        input logic clk,
        input logic rst,
        instruction_buffer_interface.buffer ib
        );

    logic buffer_reset;
    fifo_interface #(.DATA_WIDTH($bits(instruction_buffer_packet))) ib_fifo();


    //implementation
    ////////////////////////////////////////////////////
    //Control signals

    assign buffer_reset = rst | ib.flush;

    assign ib_fifo.push = ib.push;
    assign ib_fifo.pop = ib.pop;
    assign ib_fifo.data_in = ib.data_in;

    always_ff @ (posedge clk) begin
        ib.data_out <= ib_fifo.data_out;
    end

    //assign ib.data_out = ib_fifo.data_out;

    assign ib.valid = ib_fifo.valid;
    assign ib.full = ib_fifo.full;
    assign ib.early_full = ib_fifo.early_full;

    taiga_fifo #(
            .DATA_WIDTH($bits(instruction_buffer_packet)),
            .FIFO_DEPTH(FETCH_BUFFER_DEPTH),
            .FIFO_TYPE(LUTRAM_FIFO)
        ) ib_fifo_block (.fifo(ib_fifo), .rst(buffer_reset), .*);

    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert (!(~rst & ib.flush & (ib.push | ib.pop))) else $error("ib push/pop during flush");
    end

endmodule