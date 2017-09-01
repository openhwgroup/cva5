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

module ibram(
        input logic clk,
        input logic rst,

        fetch_sub_unit_interface.sub_unit fetch_sub,
        bram_interface.user instruction_bram
        );

    logic stage2_adv;
    logic address_range_valid;

    assign fetch_sub.ready = 1;

    always_ff @ (posedge clk) begin
        if (rst) begin
            stage2_adv <= 0;
        end
        else begin
            stage2_adv <= fetch_sub.new_request;
        end
    end

    assign instruction_bram.addr = fetch_sub.stage1_addr[31:2];
    assign instruction_bram.en = fetch_sub.new_request;
    assign instruction_bram.be = '0;
    assign instruction_bram.data_in = '0;
    assign fetch_sub.data_out =  instruction_bram.data_out;

    always_ff @ (posedge clk) begin
        if (rst)
            fetch_sub.data_valid <= 0;
        else if (fetch_sub.new_request)
            fetch_sub.data_valid <= 1;
        else
            fetch_sub.data_valid <= 0;
    end


endmodule
