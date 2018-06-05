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
 
import l2_config_and_types::*;

module l2_reservation_logic
        (
        input logic clk,
        input logic rst,

        input logic [31:2] addr,
        input logic [$clog2(L2_NUM_PORTS)-1:0] id,
        input logic strobe,

        input logic lr,
        input logic sc,
        input logic store, //includes read-modify-write AMOs

        output logic abort

        );

    logic [31:2] reservation_address [L2_NUM_PORTS-1:0];
    logic [L2_NUM_PORTS-1:0] reservation;

    logic [L2_NUM_PORTS-1:0] address_match;
    logic [L2_NUM_PORTS-1:0] revoke_reservation;

    always_comb begin
        for (int i = 0; i < L2_NUM_PORTS; i++) begin
            address_match[i] = (reservation_address[i] == addr);
            revoke_reservation[i] = sc | (store & address_match[i]);
        end
    end

    always_ff @(posedge clk) begin
        for (int i = 0; i < L2_NUM_PORTS; i++) begin
            if (rst)
                reservation[i] <= 0;
            else if (strobe) begin
                if (revoke_reservation[i])
                    reservation[i] <= 0;
                else if (lr)
                    reservation[i] <= 1;
            end
        end
    end

    always_ff @(posedge clk) begin
        if (strobe & lr)
            reservation_address[id] <= addr;
    end

    assign abort = sc && (~reservation[id] || (reservation[id] && ~address_match[id]));


endmodule


