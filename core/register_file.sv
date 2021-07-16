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

module register_file

    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    
    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,

        input logic gc_init_clear,

        //Issue interface
        register_file_issue_interface.register_file rf_issue,

        //Writeback
        input commit_packet_t commit [CONFIG.NUM_WB_GROUPS]
    );
    typedef logic [31:0] rs_data_set_t [REGFILE_READ_PORTS];
    rs_data_set_t rs_data_set [CONFIG.NUM_WB_GROUPS];

    typedef logic inuse_t [REGFILE_READ_PORTS]; 
    inuse_t phys_reg_inuse_set [CONFIG.NUM_WB_GROUPS];

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Phys register inuse
    //WB group 0 contains the ALU, a single-cycle unit, thus any preceeding
    //instructions will have written their data to the register file
    assign phys_reg_inuse_set[0] = '{default : 0};

    //WB groups 1+ have multiple-cycle operation and thus a status flag is set
    //for each physical register
    toggle_memory_set # (
        .DEPTH (64),
        .NUM_WRITE_PORTS (2),
        .NUM_READ_PORTS (REGFILE_READ_PORTS),
        .WRITE_INDEX_FOR_RESET (0),
        .READ_INDEX_FOR_RESET (0)
    ) id_inuse_toggle_mem_set
    (
        .clk (clk),
        .rst (rst),
        .init_clear (gc_init_clear),
        .toggle ('{(rf_issue.issued & (rf_issue.rd_wb_group == 1) & |rf_issue.phys_rd_addr), commit[1].valid}),
        .toggle_addr ('{rf_issue.phys_rd_addr, commit[1].phys_addr}),
        .read_addr (rf_issue.phys_rs_addr),
        .in_use (phys_reg_inuse_set[1])
    );
    always_comb begin
        for (int i = 0; i < REGFILE_READ_PORTS; i++) begin
            rf_issue.inuse[i] = phys_reg_inuse_set[rf_issue.rs_wb_group[i]][i];
        end
    end

    ////////////////////////////////////////////////////
    //Register Banks
    //Implemented in seperate module as there is not universal tool support for inferring
    //arrays of memory blocks.
    generate for (i = 0; i < CONFIG.NUM_WB_GROUPS; i++) begin : register_file_gen
        register_bank #(.NUM_READ_PORTS(REGFILE_READ_PORTS)) reg_group (
            .clk, .rst,
            .write_addr(commit[i].phys_addr),
            .new_data(commit[i].data),
            .commit(commit[i].valid),
            .read_addr(rf_issue.phys_rs_addr),
            .data(rs_data_set[i])
        );
    end endgenerate

    ////////////////////////////////////////////////////
    //Register File Muxing
    always_comb begin
        for (int i = 0; i < REGFILE_READ_PORTS; i++) begin
            rf_issue.data[i] = rs_data_set[rf_issue.rs_wb_group[i]][i];
        end
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    for (genvar i = 0; i < CONFIG.NUM_WB_GROUPS; i++) begin : write_to_rd_zero_assertion
        assert property (@(posedge clk) disable iff (rst) (commit[i].valid) |-> (commit[i].phys_addr != 0)) else $error("write to register zero");
    end

endmodule
