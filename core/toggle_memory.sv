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

    import taiga_config::*;
    import taiga_types::*;
    
    # (
        parameter DEPTH = 8,
        parameter NUM_READ_PORTS = 2
    )
    (
        input logic clk,
        input logic rst,

        input logic toggle,
        input logic [$clog2(DEPTH)-1:0] toggle_id,

        input logic [$clog2(DEPTH)-1:0] read_id [NUM_READ_PORTS],
        output logic read_data [NUM_READ_PORTS]
    );
    ////////////////////////////////////////////////////
    //Implementation
    (* ramstyle = "MLAB, no_rw_check" *) logic [0:0] id_toggle_memory [DEPTH];

    initial id_toggle_memory = '{default: 0};
    always_ff @ (posedge clk) begin
        id_toggle_memory[toggle_id] <= toggle ^ id_toggle_memory[toggle_id];
    end
    
    generate
    for (genvar i = 0; i < NUM_READ_PORTS; i++) begin : read_port_gen
        assign read_data[i] = id_toggle_memory[read_id[i]];
    end
    endgenerate
    


    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
