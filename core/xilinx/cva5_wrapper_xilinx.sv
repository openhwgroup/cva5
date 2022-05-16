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



module cva5_wrapper_xilinx

	import cva5_config::*;
	import cva5_types::*;
	import l2_config_and_types::*;

	(
        input logic clk,
        input logic rst,

        local_memory_interface.master instruction_bram,
        local_memory_interface.master data_bram,

       	l2_requester_interface.master l2,

        // AXI SIGNALS - need these to unwrap the interface for packaging //
	    input logic m_axi_arready,
	    output logic m_axi_arvalid,
	    output logic [C_M_AXI_ADDR_WIDTH-1:0] m_axi_araddr,
	    output logic [7:0] m_axi_arlen,
	    output logic [2:0] m_axi_arsize,
	    output logic [1:0] m_axi_arburst,
	    output logic [3:0] m_axi_arcache,
	   output logic [5:0] m_axi_arid,

	    //read data
	    output logic m_axi_rready,
	    input logic m_axi_rvalid,
	    input logic [C_M_AXI_DATA_WIDTH-1:0] m_axi_rdata,
	    input logic [1:0] m_axi_rresp,
	    input logic m_axi_rlast,
	    input logic [5:0] m_axi_rid,

	    //Write channel
	    //write address
	    input logic m_axi_awready,
	    output logic m_axi_awvalid,
	    output logic [C_M_AXI_ADDR_WIDTH-1:0] m_axi_awaddr,
	    output logic [7:0] m_axi_awlen,
	    output logic [2:0] m_axi_awsize,
	    output logic [1:0] m_axi_awburst,
	    output logic [3:0] m_axi_awcache,
	    output logic [5:0] m_axi_awid,

	    //write data
	    input logic m_axi_wready,
	    output logic m_axi_wvalid,
	    output logic [C_M_AXI_DATA_WIDTH-1:0] m_axi_wdata,
	    output logic [(C_M_AXI_DATA_WIDTH/8)-1:0] m_axi_wstrb,
	    output logic m_axi_wlast,

	    //write response
	    output logic m_axi_bready,
	    input logic m_axi_bvalid,
	    input logic [1:0] m_axi_bresp,
	    input logic [5:0] m_axi_bid
    );

    //Unused outputs
    avalon_interface m_avalon ();
    wishbone_interface dwishbone ();
    wishbone_interface iwishbone ();
    trace_outputs_t tr;
    logic timer_interrupt;
    logic interrupt;

    //AXI interface
    axi_interface m_axi();

    assign m_axi_arready = m_axi.arready;
    assign m_axi_arvalid = m_axi.arvalid;
    assign m_axi_araddr = m_axi.araddr;
    assign m_axi_arlen = m_axi.arlen;
    assign m_axi_arsize = m_axi.arsize;
    assign m_axi_arburst = m_axi.arburst;
    assign m_axi_arcache = m_axi.arcache;
    //assign m_axi_arid = m_axi.arid;

    assign m_axi_rready = m_axi.rready;
    assign m_axi_rvalid = m_axi.rvalid;
    assign m_axi_rdata = m_axi.rdata;
	assign m_axi_rresp = m_axi.rresp;
	assign m_axi_rlast = m_axi.rlast;
	//assign m_axi_rid = m_axi.rid;

	assign m_axi_awready = m_axi.awready;
	assign m_axi_awvalid = m_axi.awvalid;
	assign m_axi_awaddr = m_axi.awaddr;
	assign m_axi_awlen = m_axi.awlen;
	assign m_axi_awsize = m_axi.awsize;
	assign m_axi_awburst = m_axi.awburst;
	assign m_axi_awcache = m_axi.awcache;
	//assign m_axi_awid = m_axi.awid;

	  //write data
	assign m_axi_wready = m_axi.wready;
	assign m_axi_wvalid = m_axi.wvalid;
	assign m_axi_wdata = m_axi.wdata;
	assign m_axi_wstrb = m_axi.wstrb;
	assign m_axi_wlast = m_axi.wlast;

	    //write response
	assign m_axi_bready = m_axi.bready;
	assign m_axi_bvalid = m_axi.bvalid;
	assign m_axi_bresp = m_axi.bresp;
	//assign m_axi_bid = m_axi.bid;

    cva5 cpu(.*);

endmodule

