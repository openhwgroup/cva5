/*
 * Copyright © 2020 Eric Matthews, Lesley Shannon
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
    
    #(
        parameter NUM_WB_GROUPS = 2,
        parameter READ_PORTS = 2,
        parameter PORT_ZERO_ABSENT = 0,
        parameter USE_ZERO = 0,
        parameter type WB_PACKET_TYPE = wb_packet_t
    )

    (
        input logic clk,
        input logic rst,
        input gc_outputs_t gc,

        //decode write interface
        input phys_addr_t decode_phys_rs_addr [READ_PORTS],
        input logic [$clog2(NUM_WB_GROUPS)-1:0] decode_rs_wb_group [READ_PORTS],
        input phys_addr_t decode_phys_rd_addr,
        input logic decode_advance,
        input logic decode_uses_rd,
        input rs_addr_t decode_rd_addr, //Ignored if USE_ZERO

        //Issue interface
        register_file_issue_interface.register_file rf_issue,

        //Writeback
        input WB_PACKET_TYPE commit [NUM_WB_GROUPS],
        input phys_addr_t wb_phys_addr [NUM_WB_GROUPS]
    );
    localparam TOGGLE_PORTS = NUM_WB_GROUPS+1+32'(PORT_ZERO_ABSENT);
    localparam DATA_WIDTH = $bits(commit[0].data);
    typedef logic [DATA_WIDTH-1:0] rs_data_t [READ_PORTS];
    rs_data_t regfile_rs_data [NUM_WB_GROUPS];
    rs_data_t regfile_rs_data_r;
    rs_data_t commit_rs_data [NUM_WB_GROUPS];
    logic bypass [READ_PORTS];

    logic decode_inuse [READ_PORTS];

    phys_addr_t inuse_read_addr [READ_PORTS*2];
    logic inuse [READ_PORTS*2];
    logic toggle [TOGGLE_PORTS];
    phys_addr_t toggle_addr [TOGGLE_PORTS];
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Phys register inuse
    //toggle ports: decode advance, single-cycle/fetch_flush, multi-cycle commit
    //read ports: rs-decode, rs-issue
    always_comb begin
        for (int i = 0; i < READ_PORTS; i++) begin
            inuse_read_addr[i] = decode_phys_rs_addr[i];
            inuse_read_addr[i+READ_PORTS] = rf_issue.phys_rs_addr[i];
            decode_inuse[i] = inuse[i];
            rf_issue.inuse[i] = inuse[i+READ_PORTS];
        end
        
        toggle[0] = decode_advance & decode_uses_rd & (USE_ZERO | |decode_rd_addr) & ~gc.fetch_flush;
        toggle_addr[0] = decode_phys_rd_addr;

        toggle[1] = rf_issue.single_cycle_or_flush;
        toggle_addr[1] = rf_issue.phys_rd_addr;
        for (int i = 1; i < NUM_WB_GROUPS+PORT_ZERO_ABSENT; i++) begin
            toggle[i+1] = commit[i-PORT_ZERO_ABSENT].valid & (USE_ZERO | |wb_phys_addr[i-PORT_ZERO_ABSENT]);
            toggle_addr[i+1] = wb_phys_addr[i-PORT_ZERO_ABSENT];
        end
    end
    toggle_memory_set # (
        .DEPTH (64),
        .NUM_WRITE_PORTS (TOGGLE_PORTS),
        .NUM_READ_PORTS (READ_PORTS*2)
    ) id_inuse_toggle_mem_set
    (
        .clk (clk),
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
    generate for (genvar i = 0; i < NUM_WB_GROUPS; i++) begin : register_file_gen
        lutram_1w_mr #(.DATA_TYPE(logic[DATA_WIDTH-1:0]), .DEPTH(64), .NUM_READ_PORTS(READ_PORTS))
        register_file_bank (
            .clk,
            .waddr(wb_phys_addr[i]),
            .raddr(decode_phys_rs_addr),
            .ram_write(commit[i].valid & ~gc.writeback_suppress),
            .new_ram_data(commit[i].data),
            .ram_data_out(regfile_rs_data[i])
    );
    end endgenerate

    generate for (genvar i = 0; i < READ_PORTS; i++) begin : register_file_ff_gen
        always_ff @ (posedge clk) begin
            if (((~|decode_phys_rs_addr[i] & ~USE_ZERO) & decode_advance))
                regfile_rs_data_r[i] <= '0;
            else if (decode_advance)
                regfile_rs_data_r[i] <= regfile_rs_data[decode_rs_wb_group[i]][i];
        end
    end endgenerate

    ////////////////////////////////////////////////////
    //Bypass registers
    //(per wb group and per read port)
    always_ff @ (posedge clk) begin
        for (int i = 0; i < NUM_WB_GROUPS; i++)
            for (int j = 0; j < READ_PORTS; j++)
                if (decode_advance | rf_issue.inuse[j])
                    commit_rs_data[i][j] <= commit[i].data;
   end

    ////////////////////////////////////////////////////
    //Register File Muxing
    //Output mux per read port: bypass wb_group registers with registerfile data a
    localparam MUX_W = $clog2(NUM_WB_GROUPS+1);

    typedef logic [DATA_WIDTH-1:0] issue_data_mux_t [2**MUX_W];
    issue_data_mux_t issue_data_mux [READ_PORTS];
    logic [MUX_W-1:0] issue_sel [READ_PORTS];
    
    always_ff @ (posedge clk) begin
        for (int i = 0; i < READ_PORTS; i++)
            if (decode_advance)
                issue_sel[i] <= decode_inuse[i] ? (MUX_W)'(decode_rs_wb_group[i]) : (MUX_W)'(2**MUX_W-1);
   end

    always_comb begin
        for (int i = 0; i < READ_PORTS; i++) begin
            issue_data_mux[i] = '{default: 'x};
            issue_data_mux[i][2**MUX_W-1] = regfile_rs_data_r[i];
            for (int j = 0; j < NUM_WB_GROUPS; j++)
                issue_data_mux[i][j] = commit_rs_data[j][i];
        end
    end

    always_comb for (int i = 0; i < READ_PORTS; i++)
        rf_issue.data[i] = issue_data_mux[i][issue_sel[i]];

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
