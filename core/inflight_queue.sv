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

    logic[$bits(inflight_queue_packet)-1:0] shift_reg[INFLIGHT_QUEUE_DEPTH:0];

    //implementation
   //    CARRY4 CARRY4_inst (
   //         .CO(iq.shift_pop[4:1]),         // 4-bit carry out
    //        .O(),           // 4-bit carry chain XOR data out
   //         .CI(),         // 1-bit carry cascade input
   //         .CYINIT(1'b0), // 1-bit carry initialization
   //         .DI(4'b1111),         // 4-bit carry-MUX data in
    //        .S(iq.pop[4:1] | ~iq.valid[4:1])            // 4-bit carry-MUX select input
   //      );

    always_comb begin
        iq.shift_pop[INFLIGHT_QUEUE_DEPTH] = iq.pop[INFLIGHT_QUEUE_DEPTH] | ~iq.valid[INFLIGHT_QUEUE_DEPTH];
        for (int i=INFLIGHT_QUEUE_DEPTH-1; i >=0; i--) begin
            iq.shift_pop[i] = iq.shift_pop[i+1] | (iq.pop[i] | ~iq.valid[i]);
        end
    end

    assign iq.valid[0] = iq.new_issue;
    assign shift_reg[0] = iq.data_in;

    genvar i;
    generate
        for (i=1 ; i <= INFLIGHT_QUEUE_DEPTH; i++) begin : iq_valid_g
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
        for (i=1 ; i <= INFLIGHT_QUEUE_DEPTH; i++) begin : shift_reg_gen
            assign iq.data_out[i] = shift_reg[i];
            always_ff @ (posedge clk) begin
                if (iq.shift_pop[i])
                    shift_reg[i] <= shift_reg[i-1];
            end
        end
    endgenerate

    //future rd_addt table
    logic [4:0] rd_addrs [INFLIGHT_QUEUE_DEPTH-1:0];
    logic rd_addr_not_zero [INFLIGHT_QUEUE_DEPTH-1:0];
    always_ff @ (posedge clk) begin
        if (iq.new_issue) begin
            rd_addrs[iq.data_in.id] <= iq.future_rd_addr;
            rd_addr_not_zero[iq.data_in.id] <= iq.uses_rd;
        end
    end

    assign iq.wb_rd_addr = rd_addrs[iq.wb_id];
    assign iq.wb_uses_rd = rd_addr_not_zero[iq.wb_id];


endmodule


