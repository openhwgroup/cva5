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
import riscv_types::*;
import taiga_types::*;

module pre_decode
        (
        input logic clk,
        input logic rst,

        //Fetch
        input logic [31:0] pre_decode_instruction,
        input logic [31:0] pre_decode_pc,
        input branch_predictor_metadata_t branch_metadata,
        input logic branch_prediction_used,
        input logic [BRANCH_PREDICTOR_WAYS-1:0] bp_update_way,
        input logic pre_decode_push,

        //Global Control
        input logic gc_fetch_flush,

        //Decode
        input logic pre_decode_pop,
        output logic fb_valid,
        output fetch_buffer_packet_t fb
        );

    logic buffer_reset;

    fetch_buffer_packet_t new_data;
    fetch_buffer_packet_t data_in;
    fetch_buffer_packet_t data_out;
    fifo_interface #(.DATA_WIDTH($bits(fetch_buffer_packet_t))) fb_fifo();

    ////////////////////////////////////////////////////
    //Implementation
    //FIFO
    assign buffer_reset = rst | gc_fetch_flush;
    assign fb_fifo.supress_push = 0;//Covered by reseting on gc_fetch_flush

    assign fb_fifo.push = pre_decode_push;
    assign fb_fifo.pop = pre_decode_pop;
    assign fb_fifo.data_in = data_in;
    assign fb = fb_fifo.data_out;
    assign fb_valid = fb_fifo.valid;

    taiga_fifo #(
            .DATA_WIDTH($bits(fetch_buffer_packet_t)),
            .FIFO_DEPTH(FETCH_BUFFER_DEPTH)
        ) fb_fifo_block (.fifo(fb_fifo), .rst(buffer_reset), .*);

    ////////////////////////////////////////////////////
    //Pre-Decode
    assign data_in.instruction = pre_decode_instruction;
    assign data_in.pc = pre_decode_pc;

    ////////////////////////////////////////////////////
    //Branch Predictor support
    assign data_in.branch_metadata = branch_metadata;
    assign data_in.branch_prediction_used = branch_prediction_used;
    assign data_in.bp_update_way = bp_update_way;

    ////////////////////////////////////////////////////
    //Assertions

endmodule
