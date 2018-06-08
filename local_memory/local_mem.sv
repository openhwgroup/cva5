/*
 * Copyright © 2018 Eric Matthews,  Lesley Shannon
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
 

module  local_mem
        #(
        parameter RAM_SIZE = 64,
        parameter preload_file = "",
        parameter USE_PRELOAD_FILE = 0
        )
        (
        input logic clk,
        input logic rst,
        local_memory_interface.slave portA,
        local_memory_interface.slave portB
        );
        
        localparam LINES = (RAM_SIZE/4)*1024; //RAM width is 32-bits, so for RAM_SIZE in KB, divide by 4 and multiply by 1024.

        byte_en_BRAM #(LINES, preload_file, USE_PRELOAD_FILE) inst_data_ram (
            .clk(clk),
            .addr_a(portA.addr[$clog2(LINES)- 1:0]),
            .en_a(portA.en),
            .be_a(portA.be),
            .data_in_a(portA.data_in),
            .data_out_a(portA.data_out),

            .addr_b(portB.addr[$clog2(LINES)- 1:0]),
            .en_b(portB.en),
            .be_b(portB.be),
            .data_in_b(portB.data_in),
            .data_out_b(portB.data_out)
        );

endmodule
