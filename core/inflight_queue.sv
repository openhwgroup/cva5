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
        inflight_queue_interface.queue iq
        );

    logic [$bits(inflight_queue_packet)-1:0] shift_reg [INFLIGHT_QUEUE_DEPTH-1:0];
    logic [$bits(inflight_queue_packet)-1:0] shift_reg_new [INFLIGHT_QUEUE_DEPTH:0];

    logic [INFLIGHT_QUEUE_DEPTH-1:0] shift_pop;
    logic [INFLIGHT_QUEUE_DEPTH:0] new_valid;

    logic [INFLIGHT_QUEUE_DEPTH-1:0] valid_reversed;
    logic [INFLIGHT_QUEUE_DEPTH-1:0] pop_reversed;
    logic [INFLIGHT_QUEUE_DEPTH-1:0] shift_pop_reversed;

    //Carry chain more scalable for larger depths, but requires manual instantiation as it
    //is not possible to infer with FPGA tools
    always_comb begin
//        foreach (iq.valid[i]) begin
//            valid_reversed[i] = iq.valid[INFLIGHT_QUEUE_DEPTH-1-i];
//            pop_reversed[i] = iq.pop[INFLIGHT_QUEUE_DEPTH-1-i];
//        end
//
//        foreach (shift_pop_reversed[i]) begin
//            shift_pop[i] = shift_pop_reversed[INFLIGHT_QUEUE_DEPTH-1-i];
//        end

        shift_pop[INFLIGHT_QUEUE_DEPTH-1] = iq.pop[INFLIGHT_QUEUE_DEPTH-1] | ~iq.valid[INFLIGHT_QUEUE_DEPTH-1];
        for (int i=INFLIGHT_QUEUE_DEPTH-2; i >=0; i--) begin
            shift_pop[i] = shift_pop[i+1] | (iq.pop[i] | ~iq.valid[i]);
        end
    end

//    CARRY4 CARRY4_inst (
//            .CO(shift_pop_reversed[3:0]),         // 4-bit carry out
//            .O(),           // 4-bit carry chain XOR data out
//            .CI(),         // 1-bit carry cascade input
//            .CYINIT(1'b0), // 1-bit carry initialization
//            .DI(4'b1111),         // 4-bit carry-MUX data in
//            .S(pop_reversed[3:0] | ~valid_reversed[3:0])            // 4-bit carry-MUX select input
//        );

    genvar i;
    generate
    //Push into shift register only if the instruction is not being accepted this cycle by the writeback stage
        assign new_valid[0] = iq.new_issue & ~iq.wb_accepting_input;
        for (i=0 ; i < INFLIGHT_QUEUE_DEPTH; i++) begin : iq_valid_g
            assign new_valid[i+1] = iq.valid[i] & ~iq.pop[i];
            always_ff @ (posedge clk) begin
                if (rst)
                    iq.valid[i] <= 0;
                else if (shift_pop[i])
                    iq.valid[i] <= new_valid[i];
            end
        end

        assign shift_reg_new[0] = iq.data_in;
        for (i=0 ; i < INFLIGHT_QUEUE_DEPTH; i++) begin : shift_reg_gen
            assign shift_reg_new[i+1] = shift_reg[i];
            assign iq.data_out[i] = shift_reg[i];

            always_ff @ (posedge clk) begin
                if (shift_pop[i])
                    shift_reg[i] <= shift_reg_new[i];
            end
        end
    endgenerate

endmodule


