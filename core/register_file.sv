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

module register_file
    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    #(
        parameter NUM_READ_PORTS = 2
    )
    (
        input logic clk,
        input logic rst,

        //Writeback
        input logic [4:0] rd_addr,
        input logic [31:0] new_data,
        input logic commit,

        //Issue
        input  rs_addr_t [NUM_READ_PORTS-1:0] read_addr,
        output logic [31:0] data [NUM_READ_PORTS]
    );

    logic [31:0] register_file [32];
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Register File
    //Assign zero to r0 and initialize all registers to zero

    initial register_file = '{default: 0};
    always_ff @ (posedge clk) begin
        if (commit)
            register_file[rd_addr] <= new_data;
    end
    always_comb begin
        foreach(read_addr[i])
            data[i] = register_file[read_addr[i]];
    end

    ////////////////////////////////////////////////////
    //Assertions
    write_to_zero_reg_assertion:
        assert property (@(posedge clk) disable iff (rst) !(commit & rd_addr == 0))
        else $error("Write to zero reg occured!");

    ////////////////////////////////////////////////////
    //Simulation Only
    //synthesis translate_off
    logic [31:0][31:0] sim_registers_unamed;
    simulation_named_regfile sim_register;
    always_comb begin
        foreach(register_file[i])
            sim_registers_unamed[i] = register_file[i];
        sim_register = sim_registers_unamed;
    end
    //synthesis translate_on

endmodule
