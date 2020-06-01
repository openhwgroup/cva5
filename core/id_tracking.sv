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


module id_tracking
    import taiga_config::*;
    import taiga_types::*;
    (
        input logic clk,
        input logic rst,

        input logic gc_fetch_flush,


        //ID issuing
        output id_t next_id,
        output logic id_available,
        input id_assigned,

        // m

        //Decode ID
        input id_t decode_id,
        input decode_issued,
        output decode_id_valid,

        //Issue stage
        input id_t issue_id,
        input instruction_issued,

    );
    //////////////////////////////////////////
    localparam LOG2_MAX_IDS = $clog2(MAX_IDS);

    fifo_interface #(.DATA_WIDTH($bits(id_t))) fetched_ids();
    ////////////////////////////////////////////////////
    //Implementation
    always_ff @ (posedge clk) begin
        if (rst)
            next_id <= 0;
        else
            next_id <= next_id + LOG2_MAX_IDS'(id_assigned);
    end

    assign fetched_ids.push = id_assigned;
    assign fetched_ids.pop = decode_issued;
    assign fetched_ids.data_in = next_id;

    assign decode_id = fetched_ids.data_out;
    assign decode_id_valid = fetched_ids.valid;

    taiga_fifo #(.DATA_WIDTH($bits(id_t)), .FIFO_DEPTH(MAX_IDS))
        fetched_ids_fifo (.fifo(fetched_ids), .rst(rst | gc_fetch_flush), .*);




    always_ff @ (posedge clk) begin
        if (rst)
            id_available <= 0;
        else
            id_available <=
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert (rst | !(~rst & ~id_available & id_assigned)) else $error("Issued without valid ID!");
    end
endmodule
