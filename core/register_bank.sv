/*
 * Copyright © 2017-2020 Eric Matthews,  Lesley Shannon
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

module register_bank

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    
    #(
        parameter NUM_READ_PORTS = 2
    )
    (
        input logic clk,
        input logic rst,

        //Writeback
        input phys_addr_t write_addr,
        input logic [31:0] new_data,
        input logic commit,

        //Issue
        input phys_addr_t read_addr [NUM_READ_PORTS],
        output logic [31:0] data [NUM_READ_PORTS]
    );

    (* ramstyle = "MLAB, no_rw_check" *) logic [31:0] register_file_bank [64];
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Register File
    //Assign zero to r0 and initialize all registers to zero for simulation
    initial register_file_bank = '{default: 0};
    always_ff @ (posedge clk) begin
        if (commit)
            register_file_bank[write_addr] <= new_data;
    end
    
    generate for (genvar i = 0; i < NUM_READ_PORTS; i++)
        assign data[i] = register_file_bank[read_addr[i]];
    endgenerate

    ////////////////////////////////////////////////////
    //Assertions
    write_to_zero_reg_assertion:
        assert property (@(posedge clk) disable iff (rst) !(commit & write_addr == 0))
        else $error("Write to zero reg occured!");

endmodule
