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

module id_generator (
        input logic clk,
        input logic rst,

        id_generator_interface.generator id_gen
        );

    logic inuse [0:INFLIGHT_QUEUE_DEPTH-1];

    always_ff @ (posedge clk) begin
			for (int i=0; i <INFLIGHT_QUEUE_DEPTH; i=i+1) begin
        //foreach(inuse[i]) begin
            if(rst)
                inuse[i] <= 0;
            begin
                if(id_gen.advance && id_gen.issue_id == i)
                    inuse[i] <= 1;
                else if (id_gen.complete && id_gen.complete_id == i)
                    inuse[i] <= 0;
            end
        end
    end

    always_comb begin
        id_gen.issue_id = id_gen.complete_id;
			for (int i=0; i <INFLIGHT_QUEUE_DEPTH; i=i+1) begin
        //foreach(inuse[i]) begin
            if(~inuse[i])
                id_gen.issue_id = i;
        end
    end

    always_comb begin
        id_gen.id_avaliable = id_gen.complete;
			for (int i=0; i <INFLIGHT_QUEUE_DEPTH; i=i+1) begin
        //foreach(inuse[i]) begin
            if(~inuse[i])
                id_gen.id_avaliable = 1;
        end

    end

endmodule


