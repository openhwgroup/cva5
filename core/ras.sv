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
import riscv_types::*;
import taiga_types::*;

module ras (
        input logic clk,
        input logic rst,
        input logic gc_fetch_flush,
        ras_interface.self ras
        );

    (* ramstyle = "MLAB, no_rw_check" *) logic[31:0] lut_ram [RAS_DEPTH];

    localparam RAS_DEPTH_W = $clog2(RAS_DEPTH);
    logic [RAS_DEPTH_W-1:0] read_index;
    logic [RAS_DEPTH_W-1:0] new_index;
    fifo_interface #(.DATA_WIDTH(RAS_DEPTH_W)) ri_fifo();
    ///////////////////////////////////////////////////////
    //For simulation purposes
    initial lut_ram = '{default: 0};
     ///////////////////////////////////////////////////////
    assign ras.addr = lut_ram[read_index];
    
    //On a speculative branch, save the current stack pointer
    //Restored if branch is misspredicted (gc_fetch_flush)
    taiga_fifo #(.DATA_WIDTH(RAS_DEPTH_W), .FIFO_DEPTH(MAX_IDS))
        read_index_fifo (.clk, .rst(rst | gc_fetch_flush), .fifo(ri_fifo));

    assign ri_fifo.data_in = read_index;
    assign ri_fifo.push = ras.branch_fetched;
    assign ri_fifo.potential_push = ras.branch_fetched;
    assign ri_fifo.pop = ras.branch_retired;

    always_ff @ (posedge clk) begin
        if (ras.push)
            lut_ram[new_index] <= ras.new_addr;
    end
    
    //Rolls over when full, most recent calls will be correct, but calls greater than depth
    //will be lost.
    logic [RAS_DEPTH_W-1:0] new_index_base;
    assign new_index_base = (gc_fetch_flush & ri_fifo.valid) ? ri_fifo.data_out : read_index;
    assign new_index = new_index_base + RAS_DEPTH_W'(ras.push) - RAS_DEPTH_W'(ras.pop);
    always_ff @ (posedge clk) begin
        read_index <= new_index;
    end

endmodule