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



module nexys_wrapper

	import cva5_config::*;
	import cva5_types::*;
	import l2_config_and_types::*;
	import nexys_config::*;

	(
        input logic clk,
        input logic rst,

        // AXI SIGNALS - need these to unwrap the interface for packaging //
	    input logic m_axi_arready,
	    output logic m_axi_arvalid,
	    output logic [31:0] m_axi_araddr,
	    output logic [7:0] m_axi_arlen,
	    output logic [2:0] m_axi_arsize,
	    output logic [1:0] m_axi_arburst,
	    output logic [3:0] m_axi_arcache,
	    output logic [5:0] m_axi_arid,

	    //read data
	    output logic m_axi_rready,
	    input logic m_axi_rvalid,
	    input logic [31:0] m_axi_rdata,
	    input logic [1:0] m_axi_rresp,
	    input logic m_axi_rlast,
	    input logic [5:0] m_axi_rid,

	    //Write channel
	    //write address
	    input logic m_axi_awready,
	    output logic m_axi_awvalid,
	    output logic [31:0] m_axi_awaddr,
	    output logic [7:0] m_axi_awlen,
	    output logic [2:0] m_axi_awsize,
	    output logic [1:0] m_axi_awburst,
	    output logic [3:0] m_axi_awcache,
	    output logic [5:0] m_axi_awid,

	    //write data
	    input logic m_axi_wready,
	    output logic m_axi_wvalid,
	    output logic [31:0] m_axi_wdata,
	    output logic [3:0] m_axi_wstrb,
	    output logic m_axi_wlast,

	    //write response
	    output logic m_axi_bready,
	    input logic m_axi_bvalid,
	    input logic [1:0] m_axi_bresp,
	    input logic [5:0] m_axi_bid
    );

    //Unused outputs
    local_memory_interface instruction_bram ();
    local_memory_interface data_bram ();
    avalon_interface m_avalon ();
    wishbone_interface dwishbone ();
    wishbone_interface iwishbone ();
	axi_interface m_axi ();
    interrupt_t m_interrupt;
    interrupt_t s_interrupt;

	//L2 and AXI
    l2_requester_interface l2 ();
    axi_interface axi ();

    logic rst_r1, rst_r2;

    assign axi.arready = m_axi_arready;
    assign m_axi_arvalid = axi.arvalid;
    assign m_axi_araddr = axi.araddr;
    assign m_axi_arlen = axi.arlen;
    assign m_axi_arsize = axi.arsize;
    assign m_axi_arburst = axi.arburst;
    assign m_axi_arcache = axi.arcache;
    assign m_axi_arid = axi.arid;

    assign m_axi_rready = axi.rready;
    assign axi.rvalid = m_axi_rvalid;
    assign axi.rdata = m_axi_rdata;
	assign axi.rresp = m_axi_rresp;
	assign axi.rlast = m_axi_rlast;
	assign axi.rid = m_axi_rid;

	assign axi.awready = m_axi_awready;
	assign m_axi_awvalid = axi.awvalid;
	assign m_axi_awaddr = axi.awaddr;
	assign m_axi_awlen = axi.awlen;
	assign m_axi_awsize = axi.awsize;
	assign m_axi_awburst = axi.awburst;
	assign m_axi_awcache = axi.awcache;
	assign m_axi_awid = axi.awid;

	//write data
	assign axi.wready = m_axi_wready;
	assign m_axi_wvalid = axi.wvalid;
	assign m_axi_wdata = axi.wdata;
	assign m_axi_wstrb = axi.wstrb;
	assign m_axi_wlast = axi.wlast;

	//write response
	assign m_axi_bready = axi.bready;
	assign axi.bvalid = m_axi_bvalid;
	assign axi.bresp = m_axi_bresp;
	assign axi.bid = m_axi_bid;

    always_ff @ (posedge clk) begin
        rst_r1 <= rst;
        rst_r2 <= rst_r1;
    end

    l1_to_axi  arb(.*, .cpu(l2), .axi(axi));
    cva5 #(.CONFIG(NEXYS_CONFIG)) cpu(.rst(rst_r2), .*);

endmodule

