/*
 * Copyright © 2020 Eric Matthews,  Lesley Shannon
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

module load_queue

    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;

    # (
        parameter SQ_DEPTH = 4
    )
    ( 
        input logic clk,
        input logic rst,

        input lsq_entry_t lsq,
        output lq_entry_t lq_entry,
        input logic [SQ_DEPTH-1:0] potential_store_conflicts,
        input load_ack,
        output lq_output_valid
    );

    localparam LQ_WIDTH = $bits(lq_entry_t);
    fifo_interface #(.DATA_WIDTH(LQ_WIDTH)) load_fifo ();

    ////////////////////////////////////////////////////
    //Implementation

    taiga_fifo #(.DATA_WIDTH(LQ_WIDTH), .FIFO_DEPTH(MAX_IDS)) load_queue_fifo (
        .clk(clk),
        .rst(rst),
        .fifo(load_fifo)
    );

    //FIFO control signals
    assign load_fifo.push = lsq.new_issue & lsq.load;
    assign load_fifo.potential_push = lsq.possible_issue;
    assign load_fifo.pop = load_ack;
    assign lq_output_valid = load_fifo.valid;

    //FIFO data ports
    assign load_fifo.data_in = {lsq.addr, lsq.fn3, lsq.id, potential_store_conflicts};
    assign lq_entry = load_fifo.data_out;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
