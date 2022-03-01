/*
 * Copyright © 2019 Eric Matthews,  Lesley Shannon
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

module branch_predictor_ram

    import cva5_config::*;
    import cva5_types::*;

    #(
        parameter C_DATA_WIDTH = 20,
        parameter C_DEPTH = 512
    )
    (
        input logic clk,
        input logic rst,
        input logic [$clog2(C_DEPTH)-1:0] write_addr,
        input logic write_en,
        input logic [$clog2(C_DEPTH)-1:0] read_addr,
        input logic read_en,
        input logic [C_DATA_WIDTH-1:0] write_data,
        output logic [C_DATA_WIDTH-1:0] read_data
    );
    (* ram_style = "block" *)logic [C_DATA_WIDTH-1:0] branch_ram [C_DEPTH-1:0];
    ////////////////////////////////////////////////////
    //Implementation
    initial branch_ram = '{default: 0};
    always_ff @(posedge clk) begin
        if (write_en)
            branch_ram[write_addr] <= write_data;
    end
    always_ff @(posedge clk) begin
        if (read_en)
            read_data <= branch_ram[read_addr];
    end
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////
    //Trace Interface

endmodule
