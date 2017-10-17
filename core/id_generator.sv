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


