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

module ras (
        input logic clk,
        input logic rst,
        ras_interface.self ras
        );

    logic[31:0] lut_ram [RAS_DEPTH-1:0];

    logic[$clog2(RAS_DEPTH)-1:0] read_index;
    logic[$clog2(RAS_DEPTH)-1:0] write_index;
    logic valid_chain[RAS_DEPTH-1:0];
    logic valid_chain_update;
    ///////////////////////////////////////////////////////
    //For simulation purposes
    initial
        for (int i=0; i <RAS_DEPTH; i++) begin
            lut_ram[i] = 0;
            valid_chain[i] = 0;
        end    
     ///////////////////////////////////////////////////////
    assign ras.addr = lut_ram[read_index];
    assign ras.valid = valid_chain[read_index];
    
    always_ff @ (posedge clk) begin
        if (ras.push)
            lut_ram[write_index] <= ras.new_addr;
    end
    
    //Rolls over when full, most recent calls will be correct, but calls greater than depth
    //will be lost.
    always_ff @ (posedge clk) begin
        if (rst)
            read_index <= 0;
        else if (ras.push & ~ras.pop)
            read_index <= write_index;
        else if (ras.pop & ~ras.push)
            read_index <= read_index - 1;
    end
    assign write_index = (ras.push & ~ras.pop) ? (read_index + valid_chain[read_index]) : read_index;
    
    assign valid_chain_update = ras.push | ras.pop;
    always_ff @ (posedge clk) begin
        if (valid_chain_update)
            valid_chain[write_index] <= ras.push;
    end    
        
endmodule


