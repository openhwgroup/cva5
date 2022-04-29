/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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

import cva5_config::*;
import cva5_types::*;
import l2_config_and_types::*;

module cva5_wrapper (
        input logic sys_clk,
        input logic ext_reset,


        inout [14:0]DDR_addr,
        inout [2:0]DDR_ba,
        inout DDR_cas_n,
        inout DDR_ck_n,
        inout DDR_ck_p,
        inout DDR_cke,
        inout DDR_cs_n,
        inout [3:0]DDR_dm,
        inout [31:0]DDR_dq,
        inout [3:0]DDR_dqs_n,
        inout [3:0]DDR_dqs_p,
        inout DDR_odt,
        inout DDR_ras_n,
        inout DDR_reset_n,
        inout DDR_we_n,
        inout FIXED_IO_ddr_vrn,
        inout FIXED_IO_ddr_vrp,
        inout [53:0]FIXED_IO_mio,
        inout FIXED_IO_ps_clk,
        inout FIXED_IO_ps_porb,
        inout FIXED_IO_ps_srstb,

        input logic sin,
        output logic sout

        );
        
        
    parameter SCRATCH_MEM_KB = 16;
    parameter MEM_LINES = (SCRATCH_MEM_KB*1024)/4;

    logic clk;
    logic rst;
    logic resetn;

    axi_interface m_axi();
    avalon_interface m_avalon();
    wishbone_interface dwishbone();
    wishbone_interface iwishbone();
    l2_requester_interface l2[L2_NUM_PORTS-1:0]();
    l2_memory_interface mem();

    logic interrupt;

    assign interrupt = 0;

    //mem axi
    logic [31:0]mem_axi_araddr;
    logic [1:0]mem_axi_arburst;
    logic [3:0]mem_axi_arcache;
    logic [5:0]mem_axi_arid;
    logic [7:0]mem_axi_arlen;
    logic [0:0]mem_axi_arlock;
    logic [2:0]mem_axi_arprot;
    logic [3:0]mem_axi_arqos;
    logic mem_axi_arready;
    logic [3:0]mem_axi_arregion;
    logic [2:0]mem_axi_arsize;
    logic mem_axi_arvalid;
    logic [31:0]mem_axi_awaddr;
    logic [1:0]mem_axi_awburst;
    logic [3:0]mem_axi_awcache;
    logic [5:0]mem_axi_awid;
    logic [7:0]mem_axi_awlen;
    logic [0:0]mem_axi_awlock;
    logic [2:0]mem_axi_awprot;
    logic [3:0]mem_axi_awqos;
    logic mem_axi_awready;
    logic [3:0]mem_axi_awregion;
    logic [2:0]mem_axi_awsize;
    logic mem_axi_awvalid;
    logic [5:0]mem_axi_bid;
    logic mem_axi_bready;
    logic [1:0]mem_axi_bresp;
    logic mem_axi_bvalid;
    logic [31:0]mem_axi_rdata;
    logic [5:0]mem_axi_rid;
    logic mem_axi_rlast;
    logic mem_axi_rready;
    logic [1:0]mem_axi_rresp;
    logic mem_axi_rvalid;
    logic [31:0]mem_axi_wdata;
    logic mem_axi_wlast;
    logic mem_axi_wready;
    logic [3:0]mem_axi_wstrb;
    logic mem_axi_wvalid;
    logic [5:0] mem_axi_wid;

    logic ACLK;
    logic [31:0]bus_axi_araddr;
    logic bus_axi_arready;
    logic bus_axi_arvalid;
    logic [31:0]bus_axi_awaddr;
    logic bus_axi_awready;
    logic bus_axi_awvalid;
    logic bus_axi_bready;
    logic [1:0]bus_axi_bresp;
    logic bus_axi_bvalid;
    logic [31:0]bus_axi_rdata;
    logic bus_axi_rready;
    logic [1:0]bus_axi_rresp;
    logic bus_axi_rvalid;
    logic [31:0]bus_axi_wdata;
    logic bus_axi_wready;
    logic [3:0]bus_axi_wstrb;
    logic bus_axi_wvalid;

    logic processor_reset;


    //Arbiter AXI interface
    logic axi_arready;
    logic axi_arvalid;
    logic[31:0] axi_araddr;
    logic[3:0] axi_arlen;
    logic[2:0] axi_arsize;
    logic[1:0] axi_arburst;
    logic[2:0] axi_arprot;
    logic[3:0] axi_arcache;
    logic[3:0] axi_arid;
    logic [1:0]axi_arlock;
    logic [3:0]axi_arqos;

    //read data channel
    logic axi_rready;
    logic axi_rvalid;
    logic[31:0] axi_rdata;
    logic[1:0] axi_rresp;
    logic axi_rlast;
    logic[3:0] axi_rid;

    //write addr channel
    logic axi_awready;
    logic axi_awvalid;
    logic [31:0] axi_awaddr;
    logic [7:0] axi_awlen;
    logic [2:0] axi_awsize;
    logic [1:0] axi_awburst;
    logic [1:0]axi_awlock;
    logic [3:0]axi_awqos;
    logic [5:0]axi_awid;

    logic[3:0] axi_awcache;
    logic[2:0] axi_awprot;

    //write data
    logic axi_wready;
    logic axi_wvalid;
    logic [31:0] axi_wdata;
    logic [3:0] axi_wstrb;
    logic axi_wlast;
    logic [5:0]axi_wid;


    //write response
    logic axi_bready;
    logic axi_bvalid;
    logic [1:0] axi_bresp;
    logic [5:0]axi_bid;


    logic axi_clk;
    logic processor_clk;

    assign axi_clk = clk;

    assign rst = processor_reset;


    assign m_axi.arready = bus_axi_arready;
    assign bus_axi_arvalid = m_axi.arvalid;
    assign bus_axi_araddr = m_axi.araddr[12:0];


    //read data
    assign bus_axi_rready = m_axi.rready;
    assign m_axi.rvalid = bus_axi_rvalid;
    assign m_axi.rdata = bus_axi_rdata;
    assign m_axi.rresp = bus_axi_rresp;

    //Write channel
    //write address
    assign m_axi.awready = bus_axi_awready;
    assign bus_axi_awaddr = m_axi.awaddr[12:0];
    assign bus_axi_awvalid = m_axi.awvalid;


    //write data
    assign m_axi.wready = bus_axi_wready;
    assign bus_axi_wvalid = m_axi. wvalid;
    assign bus_axi_wdata = m_axi.wdata;
    assign bus_axi_wstrb = m_axi.wstrb;

    //write response
    assign bus_axi_bready = m_axi.bready;
    assign m_axi.bvalid = bus_axi_bvalid;
    assign m_axi.bresp = bus_axi_bresp;


    local_memory_interface instruction_bram();
    local_memory_interface data_bram();

    cva5 cpu(.*, .l2(l2[0]));

    //design_2 infra(.*);

    generate
        if (EXAMPLE_CONFIG.INCLUDE_S_MODE || EXAMPLE_CONFIG.INCLUDE_ICACHE || EXAMPLE_CONFIG.INCLUDE_DCACHE) begin
            l2_arbiter l2_arb (.*, .request(l2));
            axi_to_arb l2_to_mem (.*, .l2(mem));
        end
    endgenerate

    //arm proc(.*);
    byte_en_BRAM #(MEM_LINES, "/home/ematthew/Research/RISCV/software2/riscv-tools/riscv-tests/benchmarks/fft.riscv.hw_init", 1) inst_data_ram (
            .clk(clk),
            .addr_a(instruction_bram.addr[$clog2(MEM_LINES)- 1:0]),
            .en_a(instruction_bram.en),
            .be_a(instruction_bram.be),
            .data_in_a(instruction_bram.data_in),
            .data_out_a(instruction_bram.data_out),

            .addr_b(data_bram.addr[$clog2(MEM_LINES)- 1:0]),
            .en_b(data_bram.en),
            .be_b(data_bram.be),
            .data_in_b(data_bram.data_in),
            .data_out_b(data_bram.data_out)
        );

endmodule