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
        input rs_addr_t decode_rd_addr,

        //Issue interface
        register_file_issue_interface.register_file rf_issue,

        //Writeback
        input wb_packet_t commit [CONFIG.NUM_WB_GROUPS],
        input phys_addr_t wb_phys_addr [CONFIG.NUM_WB_GROUPS]
    );
    typedef logic [31:0] rs_data_t [REGFILE_READ_PORTS];
    rs_data_t regfile_rs_data [CONFIG.NUM_WB_GROUPS];
    rs_data_t regfile_rs_data_r;
    rs_data_t commit_rs_data [CONFIG.NUM_WB_GROUPS];
    logic bypass [REGFILE_READ_PORTS];

    logic decode_inuse [REGFILE_READ_PORTS];

    phys_addr_t inuse_read_addr [REGFILE_READ_PORTS*2];
    logic inuse [REGFILE_READ_PORTS*2];
    logic toggle [1+CONFIG.NUM_WB_GROUPS];
    phys_addr_t toggle_addr [1+CONFIG.NUM_WB_GROUPS];
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
        
        toggle[0] = decode_advance & decode_uses_rd & |decode_rd_addr & ~gc.fetch_flush;
        toggle_addr[0] = decode_phys_rd_addr;
        toggle[1] = rf_issue.single_cycle_or_flush;
        toggle_addr[1] = rf_issue.phys_rd_addr;
        for (int i = 1; i < CONFIG.NUM_WB_GROUPS; i++) begin
            toggle[i+1] = commit[i].valid & |wb_phys_addr[i];
            toggle_addr[i+1] = wb_phys_addr[i];
        end
    end
    toggle_memory_set # (
        .DEPTH (64),
        .NUM_WRITE_PORTS (1+CONFIG.NUM_WB_GROUPS),
        .NUM_READ_PORTS (REGFILE_READ_PORTS*2),
        .WRITE_INDEX_FOR_RESET (0),
        .READ_INDEX_FOR_RESET (0)
    ) id_inuse_toggle_mem_set
    (
        .clk (clk),
        .rst (rst),
        .init_clear (gc.init_clear),
        .toggle (toggle),
        .toggle_addr (toggle_addr),
        .read_addr (inuse_read_addr),
        .in_use (inuse)
    );

    ////////////////////////////////////////////////////
    //Register Banks
    //LUTRAM implementation
    //Read in decode stage, writeback groups muxed and output registered per regfile read port
    generate for (genvar i = 0; i < CONFIG.NUM_WB_GROUPS; i++) begin : register_file_gen
        lutram_1w_mr #(.DATA_TYPE(logic[31:0]), .DEPTH(64), .NUM_READ_PORTS(REGFILE_READ_PORTS))
        register_file_bank (
            .clk,
            .waddr(wb_phys_addr[i]),
            .raddr(decode_phys_rs_addr),
            .ram_write(commit[i].valid & ~gc.writeback_supress),
            .new_ram_data(commit[i].data),
            .ram_data_out(regfile_rs_data[i])
    );
    end endgenerate

    generate for (genvar i = 0; i < REGFILE_READ_PORTS; i++) begin : register_file_ff_gen
        always_ff @ (posedge clk) begin
            if ((~|decode_phys_rs_addr[i] & decode_advance))
                regfile_rs_data_r[i] <= '0;
            else if (decode_advance)
                regfile_rs_data_r[i] <= regfile_rs_data[decode_rs_wb_group[i]][i];
        end
    end endgenerate

    ////////////////////////////////////////////////////
    //Bypass registers
    //(per wb group and per read port)
    always_ff @ (posedge clk) begin
        for (int i = 0; i < CONFIG.NUM_WB_GROUPS; i++)
            for (int j = 0; j < REGFILE_READ_PORTS; j++)
                if (decode_advance | rf_issue.inuse[j])
                    commit_rs_data[i][j] <= commit[i].data;
   end

    ////////////////////////////////////////////////////
    //Register File Muxing
    //Output mux per read port: bypass wb_group registers with registerfile data a
    localparam MUX_W = $clog2(CONFIG.NUM_WB_GROUPS+1);

    typedef logic [31:0] issue_data_mux_t [2**MUX_W];
    issue_data_mux_t issue_data_mux [REGFILE_READ_PORTS];
    logic [MUX_W-1:0] issue_sel [REGFILE_READ_PORTS];
    
    always_ff @ (posedge clk) begin
        for (int i = 0; i < REGFILE_READ_PORTS; i++)
            if (decode_advance)
                issue_sel[i] <= decode_inuse[i] ? decode_rs_wb_group[i] : (MUX_W)'(2**MUX_W-1);
   end

    always_comb begin
        for (int i = 0; i < REGFILE_READ_PORTS; i++) begin
            issue_data_mux[i] = '{default: 'x};
            issue_data_mux[i][2**MUX_W-1] = regfile_rs_data_r[i];
            for (int j = 0; j < CONFIG.NUM_WB_GROUPS; j++) begin
                issue_data_mux[i][j] = commit_rs_data[j][i];
            end
        end
    end

    always_comb for (int i = 0; i < REGFILE_READ_PORTS; i++)
        rf_issue.data[i] = issue_data_mux[i][issue_sel[i]];

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
