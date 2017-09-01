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


