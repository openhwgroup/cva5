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

module toggle_memory

    # (
        parameter DEPTH = 8,
        parameter NUM_READ_PORTS = 2
    )
    (
        input logic clk,

        input logic toggle,
        input logic [$clog2(DEPTH)-1:0] toggle_id,

        input logic [$clog2(DEPTH)-1:0] read_id [NUM_READ_PORTS],
        output logic read_data [NUM_READ_PORTS]
    );
    ////////////////////////////////////////////////////
    //Implementation
    logic new_ram_data;
    logic _read_data [NUM_READ_PORTS+1];
    logic [$clog2(DEPTH)-1:0] _read_id [NUM_READ_PORTS+1];

    assign _read_id[0] = toggle_id;
    assign _read_id[1:NUM_READ_PORTS] = read_id;

    assign new_ram_data = toggle ^ _read_data[0];

    lutram_1w_mr #(
        .DATA_TYPE(logic),
        .DEPTH(DEPTH),
        .NUM_READ_PORTS(NUM_READ_PORTS+1)
    )
    write_port (
        .clk(clk),
        .waddr(toggle_id),
        .raddr(_read_id),
        .ram_write(1'b1),
        .new_ram_data(new_ram_data),
        .ram_data_out(_read_data)
    );

    assign read_data = _read_data[1:NUM_READ_PORTS];

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
