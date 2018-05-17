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

    logic [0:INFLIGHT_QUEUE_DEPTH-1] inuse;
    logic [0:INFLIGHT_QUEUE_DEPTH-1] new_inuse;
    logic [0:INFLIGHT_QUEUE_DEPTH-1] clear_inuse;
    logic [0:INFLIGHT_QUEUE_DEPTH-1] set_inuse;
    //implementation
    ////////////////////////////////////////////////////

    //Clear inuse on instruction completion, set on instruction issue
    //Set takes precedence over clearing.
    always_comb begin
        set_inuse = 0;
        set_inuse[id_gen.issue_id] = id_gen.advance;

        clear_inuse = 0;
        clear_inuse[id_gen.complete_id] = id_gen.complete;

        new_inuse = (inuse & ~clear_inuse) | set_inuse;
    end

    always_ff @ (posedge clk) begin
        if(rst)
            inuse <= 0;
        else
            inuse <= new_inuse;
    end

    always_comb begin
        id_gen.issue_id = id_gen.complete_id;
        for (int i=0; i <INFLIGHT_QUEUE_DEPTH; i=i+1) begin
            if(~inuse[i])
                id_gen.issue_id = i;
        end
    end

    //Instruction complete or at least one inuse bit is not set
    assign id_gen.id_avaliable = id_gen.complete | ~(&inuse);

endmodule


