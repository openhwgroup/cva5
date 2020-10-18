/*
 * Copyright © 2020 Eric Matthews,  Lesley Shannon
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

module toggle_memory_set
    import taiga_config::*;
    import taiga_types::*;
    # (
        parameter DEPTH = 64,
        parameter NUM_WRITE_PORTS = 3,
        parameter NUM_READ_PORTS = 2,
        parameter WRITE_INDEX_FOR_RESET = 0,
        parameter READ_INDEX_FOR_RESET = 0
    )
    (
        input logic clk,
        input logic rst,
        input logic init_clear,

        input logic toggle [NUM_WRITE_PORTS],
        input logic [$clog2(DEPTH)-1:0] toggle_addr [NUM_WRITE_PORTS],

        input logic [$clog2(DEPTH)-1:0] read_addr [NUM_READ_PORTS],
        output logic in_use [NUM_READ_PORTS]
    );
    ////////////////////////////////////////////////////
    //Implementation
    logic [$clog2(DEPTH)-1:0] _toggle_addr [NUM_WRITE_PORTS];
    logic _toggle [NUM_WRITE_PORTS];
    logic [$clog2(DEPTH)-1:0] _read_addr [NUM_READ_PORTS];
    logic read_data [NUM_WRITE_PORTS][NUM_READ_PORTS];
    logic [$clog2(DEPTH)-1:0] clear_index;

    //counter for indexing through memories for post-reset clearing/initialization
    initial clear_index = 0;
    always_ff @ (posedge clk) begin
        if (init_clear)
            clear_index <= clear_index + 1;
    end
    
    //muxing of read and write ports to support post-reset clearing/initialization
    always_comb begin
        _toggle_addr = toggle_addr;
        _read_addr = read_addr;
        _toggle = toggle;
        
        _toggle_addr[WRITE_INDEX_FOR_RESET] = init_clear ? clear_index : toggle_addr[WRITE_INDEX_FOR_RESET];
        _read_addr[READ_INDEX_FOR_RESET] = init_clear ? clear_index : read_addr[READ_INDEX_FOR_RESET];
        _toggle[WRITE_INDEX_FOR_RESET] = init_clear ? in_use[READ_INDEX_FOR_RESET] : _toggle[WRITE_INDEX_FOR_RESET];
    end


    //Instantiation of NUM_READ_PORTS*NUM_WRITE_PORTS dual-ported single-bit wide toggle memories
    genvar i, j;
    generate
    for (i = 0; i < NUM_READ_PORTS; i++) begin : read_port_gen
        for (j = 0; j < NUM_WRITE_PORTS; j++) begin : write_port_gen
            toggle_memory #(.DEPTH(DEPTH)) mem (
                .clk (clk), .rst (rst),
                .toggle(_toggle[j]),
                .toggle_id(_toggle_addr[j]),
                .read_id(_read_addr[i]),
                .read_data(read_data[j][i])
            );
        end
    end
    endgenerate

    //In-use determination.  XOR of all write blocks for each read address
    always_comb begin
        in_use = '{default: 0};
        for (int i = 0;  i < NUM_READ_PORTS; i++) begin
            for (int j = 0; j < NUM_WRITE_PORTS; j++) begin
                in_use[i] ^= read_data[j][i];
            end
        end
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
