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

module ddata_bank #(
        parameter LINES = 1024
        )
        (
        input logic clk,
        input logic[$clog2(LINES)-1:0] addr_a,
        input logic en_a,
        input logic[3:0] be_a,
        input logic[31:0] data_in_a,
        output logic[31:0] data_out_a,

        //write only port
        input logic[$clog2(LINES)-1:0] addr_b,
        input logic en_b,
        input logic[31:0] data_in_b
        );

    byte_en_BRAM #(LINES, "", 0) ram_block (.*, .be_b({4{en_b}}), .data_out_b());

endmodule
