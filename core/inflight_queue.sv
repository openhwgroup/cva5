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

//No protection on push to full queue or pop from empty
module inflight_queue
        (
        input logic clk,
        input logic rst,
        input logic instruction_complete,
        inflight_queue_interface.queue iq
        );

    logic[$bits(inflight_queue_packet)-1:0] shift_reg[INFLIGHT_QUEUE_DEPTH-1:0];

    //implementation
    assign iq.shift_pop[INFLIGHT_QUEUE_DEPTH-1] = iq.pop[INFLIGHT_QUEUE_DEPTH-1] | ~iq.valid[INFLIGHT_QUEUE_DEPTH-1];
    always_comb begin
        for (int i=INFLIGHT_QUEUE_DEPTH-2; i >=0; i--) begin
            iq.shift_pop[i] = iq.shift_pop[i+1] | (iq.pop[i] | ~iq.valid[i]);
        end
    end

    always_ff @ (posedge clk) begin
        if (rst)
            iq.valid[0] <= 0;
        else if (iq.shift_pop[0])
            iq.valid[0] <= iq.new_issue;
    end

    always_ff @ (posedge clk) begin
        if (iq.shift_pop[0])
            shift_reg[0] <= iq.data_in;
    end

    genvar i;
    generate
        for (i=1 ; i < INFLIGHT_QUEUE_DEPTH; i++) begin : iq_valid_g
            always_ff @ (posedge clk) begin
                if (rst)
                    iq.valid[i] <= 0;
                else if (iq.shift_pop[i]) begin
                    iq.valid[i] <= iq.valid[i-1] & ~iq.pop[i-1];
                end
            end
        end
    endgenerate

    //Data portion
    assign iq.data_out[0] = shift_reg[0];
    generate
        for (i=1 ; i < INFLIGHT_QUEUE_DEPTH; i++) begin : shift_reg_gen
            assign iq.data_out[i] = shift_reg[i];
            always_ff @ (posedge clk) begin
                if (iq.shift_pop[i])
                    shift_reg[i] <= shift_reg[i-1];
            end
        end
    endgenerate

endmodule


