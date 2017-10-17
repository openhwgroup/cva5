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


