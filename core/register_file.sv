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

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    
    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,
        input gc_outputs_t gc,

        //decode write interface
        input phys_addr_t decode_phys_rs_addr [REGFILE_READ_PORTS],
        input logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] decode_rs_wb_group [REGFILE_READ_PORTS],
        input phys_addr_t decode_phys_rd_addr,
        input logic decode_advance,
        input logic decode_uses_rd,

        //Issue interface
        register_file_issue_interface.register_file rf_issue,

        //Writeback
        input wb_packet_t commit [CONFIG.NUM_WB_GROUPS]
    );
    typedef logic [31:0] rs_data_set_t [REGFILE_READ_PORTS];
    rs_data_set_t rs_data_set [CONFIG.NUM_WB_GROUPS];

    logic decode_inuse [REGFILE_READ_PORTS];
    logic decode_inuse_r [REGFILE_READ_PORTS];

    phys_addr_t inuse_read_addr [REGFILE_READ_PORTS*2];
    logic inuse [REGFILE_READ_PORTS*2];
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Phys register inuse
    //toggle ports: decode advance, single-cycle/fetch_flush, multi-cycle commit
    //read ports: rs-decode, rs-issue
    always_comb begin
        for (int i = 0; i < REGFILE_READ_PORTS; i++) begin
            inuse_read_addr[i] = decode_phys_rs_addr[i];
            inuse_read_addr[i+REGFILE_READ_PORTS] = rf_issue.phys_rs_addr[i];
            decode_inuse[i] = inuse[i];
            rf_issue.inuse[i] = inuse[i+REGFILE_READ_PORTS];
        end
    end
    toggle_memory_set # (
        .DEPTH (64),
        .NUM_WRITE_PORTS (3),
        .NUM_READ_PORTS (REGFILE_READ_PORTS*2),
        .WRITE_INDEX_FOR_RESET (0),
        .READ_INDEX_FOR_RESET (0)
    ) id_inuse_toggle_mem_set
    (
        .clk (clk),
        .rst (rst),
        .init_clear (gc.init_clear),
        .toggle ('{
            (decode_advance & decode_uses_rd & |decode_phys_rd_addr & ~gc.fetch_flush),
            rf_issue.single_cycle_or_flush,
            commit[1].valid & |commit[1].phys_addr
        }),
        .toggle_addr ('{
            decode_phys_rd_addr, 
            rf_issue.phys_rd_addr, 
            commit[1].phys_addr
        }),
        .read_addr (inuse_read_addr),
        .in_use (inuse)
    );
    always_ff @ (posedge clk) begin
        if (decode_advance)
            decode_inuse_r <= decode_inuse;
    end
    ////////////////////////////////////////////////////
    //Register Banks
    //Implemented in seperate module as there is not universal tool support for inferring
    //arrays of memory blocks.
    generate for (genvar i = 0; i < CONFIG.NUM_WB_GROUPS; i++) begin : register_file_gen
        register_bank #(.NUM_READ_PORTS(REGFILE_READ_PORTS))
        reg_group (
            .clk, .rst,
            .write_addr(commit[i].phys_addr),
            .new_data(commit[i].data),
            .commit(commit[i].valid & |commit[i].phys_addr & ~gc.writeback_supress),
            .read_addr(decode_phys_rs_addr),
            .data(rs_data_set[i])
        );
    end endgenerate

    ////////////////////////////////////////////////////
    //Register File Muxing
    logic bypass [REGFILE_READ_PORTS];

    rs_data_set_t bypass_set [CONFIG.NUM_WB_GROUPS];
    wb_packet_t commit_r [CONFIG.NUM_WB_GROUPS][REGFILE_READ_PORTS];
    rs_data_set_t rs_data_set_r [CONFIG.NUM_WB_GROUPS];

    always_ff @ (posedge clk) begin
        if (decode_advance)
            rs_data_set_r <= rs_data_set;
        for (int i = 0; i < REGFILE_READ_PORTS; i++) begin
            if (decode_advance | rf_issue.inuse[i]) begin
                bypass <= decode_advance ? decode_inuse : decode_inuse_r;
                commit_r[i] <= commit;
            end
        end
   end

    always_comb begin
        for (int i = 0; i < REGFILE_READ_PORTS; i++) begin
            for (int j = 0; j < CONFIG.NUM_WB_GROUPS; j++) begin
                bypass_set[j][i] =  bypass[i] ? commit_r[i][j].data : rs_data_set_r[j][i];
            end
            rf_issue.data[i] = bypass_set[rf_issue.rs_wb_group[i]][i];
        end
    end


    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
