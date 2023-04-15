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

    import cva5_config::*;
    import cva5_types::*;
    
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
    logic [$clog2(DEPTH)-1:0] _toggle_addr [NUM_WRITE_PORTS+1];
    logic _toggle [NUM_WRITE_PORTS+1];
    logic [$clog2(DEPTH)-1:0] _read_addr [NUM_READ_PORTS+1];
    logic read_data [NUM_WRITE_PORTS+1][NUM_READ_PORTS+1];
    logic _in_use [NUM_READ_PORTS+1];
    logic [$clog2(DEPTH)-1:0] clear_index;

    //counter for indexing through memories for post-reset clearing/initialization
    lfsr #(.WIDTH($clog2(DEPTH)), .NEEDS_RESET(0))
    lfsr_counter (
        .clk (clk), .rst (rst),
        .en(init_clear),
        .value(clear_index)
    );
    
    //muxing of read and write ports to support post-reset clearing/initialization
    always_comb begin
        _toggle_addr[0:NUM_WRITE_PORTS-1] = toggle_addr;
        _toggle[0:NUM_WRITE_PORTS-1] = toggle;
        _read_addr[0:NUM_READ_PORTS-1] = read_addr;
        
        _toggle_addr[NUM_WRITE_PORTS] = clear_index;
        _toggle[NUM_WRITE_PORTS] = init_clear & _in_use[NUM_READ_PORTS];
        _read_addr[NUM_READ_PORTS] = clear_index;
    end


    //Instantiation of NUM_READ_PORTS*NUM_WRITE_PORTS dual-ported single-bit wide toggle memories
    genvar i, j;
    generate
        for (j = 0; j < NUM_WRITE_PORTS+1; j++) begin : write_port_gen
            toggle_memory #(.DEPTH(DEPTH), .NUM_READ_PORTS(NUM_READ_PORTS+1))
            mem (
                .clk (clk), .rst (rst),
                .toggle(_toggle[j]),
                .toggle_id(_toggle_addr[j]),
                .read_id(_read_addr),
                .read_data(read_data[j])
            );
        end
    endgenerate

    //In-use determination.  XOR of all write blocks for each read address
    always_comb begin
        _in_use = '{default: 0};
        for (int i = 0;  i < NUM_READ_PORTS+1; i++) begin
            for (int j = 0; j < NUM_WRITE_PORTS+1; j++) begin
                _in_use[i] ^= read_data[j][i];
            end
        end
        for (int i = 0;  i < NUM_READ_PORTS; i++) begin
            in_use[i] = _in_use[i];
        end
    end
    
    

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
