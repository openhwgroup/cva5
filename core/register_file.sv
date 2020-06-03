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
    (
        input logic clk,
        input logic rst,

        //Issue interface
        input issue_packet_t issue,
        input logic [4:0] rd_addr,
        input logic [31:0] new_data,
        input logic commit,

        output logic [31:0] rs1_data,
        output logic [31:0] rs2_data
    );

    logic [31:0] register_file [32];
    genvar i;
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
    assign rs1_data = register_file[issue.rs1_addr];
    assign rs2_data = register_file[issue.rs2_addr];

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
