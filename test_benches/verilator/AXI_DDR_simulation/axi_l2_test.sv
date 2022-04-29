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


module axi_l2_test # (
        parameter MEMORY_FILE = "/home/ematthew/Research/RISCV/software/riscv-tools/riscv-tests/benchmarks/dhrystone.riscv.hw_init" //change this to appropriate location "/home/ematthew/Downloads/dhrystone.riscv.sim_init"
        )
        (
        input logic clk,
        input logic rst,

        //DDR AXI
        output logic [31:0]ddr_axi_araddr,
        output logic [1:0]ddr_axi_arburst,
        output logic [3:0]ddr_axi_arcache,
        output logic [5:0]ddr_axi_arid,
        output logic [7:0]ddr_axi_arlen,
        output logic [0:0]ddr_axi_arlock,
        output logic [2:0]ddr_axi_arprot,
        output logic [3:0]ddr_axi_arqos,
        input logic ddr_axi_arready,
        output logic [3:0]ddr_axi_arregion,
        output logic [2:0]ddr_axi_arsize,
        output logic ddr_axi_arvalid,
        output logic [31:0]ddr_axi_awaddr,
        output logic [1:0]ddr_axi_awburst,
        output logic [3:0]ddr_axi_awcache,
        output logic [5:0]ddr_axi_awid,
        output logic [7:0]ddr_axi_awlen,
        output logic [0:0]ddr_axi_awlock,
        output logic [2:0]ddr_axi_awprot,
        output logic [3:0]ddr_axi_awqos,
        input logic ddr_axi_awready,
        output logic [3:0]ddr_axi_awregion,
        output logic [2:0]ddr_axi_awsize,
        output logic ddr_axi_awvalid,
        output logic [5:0]ddr_axi_bid,
        output logic ddr_axi_bready,
        input logic [1:0]ddr_axi_bresp,
        input logic ddr_axi_bvalid,
        input logic [31:0]ddr_axi_rdata,
        input logic [5:0]ddr_axi_rid,
        input logic ddr_axi_rlast,
        output logic ddr_axi_rready,
        input logic [1:0]ddr_axi_rresp,
        input logic ddr_axi_rvalid,
        output logic [31:0]ddr_axi_wdata,
        output logic ddr_axi_wlast,
        input logic ddr_axi_wready,
        output logic [3:0]ddr_axi_wstrb,
        output logic ddr_axi_wvalid,
        output logic [5:0]ddr_axi_wid,


		//L2 interface
	   	input logic [29:0] addr,
		input logic [3:0] be,
		input logic rnw,
		input logic is_amo,
		input logic [4:0] amo_type_or_burst_size,
		input logic [L2_SUB_ID_W-1:0] sub_id,

		input logic request_push,
		output logic request_full,

		output logic [31:2] inv_addr,
		output logic inv_valid,
		input logic inv_ack,

		output logic con_result,
		output logic con_valid,

		input logic [31:0] wr_data,
		input logic wr_data_push,
		output logic data_full,

		output logic [31:0] rd_data,
		output logic [L2_SUB_ID_W-1:0] rd_sub_id,
		output logic rd_data_valid,
		input logic rd_data_ack,

        //Local Memory
        output logic [29:0] instruction_bram_addr,
        output logic instruction_bram_en,
        output logic [3:0] instruction_bram_be,
        output logic [31:0] instruction_bram_data_in,
        input logic [31:0] instruction_bram_data_out,

        output logic [29:0] data_bram_addr,
        output logic data_bram_en,
        output logic [3:0] data_bram_be,
        output logic [31:0] data_bram_data_in,
        input logic [31:0] data_bram_data_out,

        //Used by verilator
        output logic write_uart,
        output logic [7:0] uart_byte,

        //Trace Interface
        output logic instruction_issued,
        output logic cva5_events [0:$bits(cva5_trace_events_t)-1],
        output logic [31:0] instruction_pc_dec,
        output logic [31:0] instruction_data_dec
    );

    logic [3:0] WRITE_COUNTER_MAX;
    logic [3:0] READ_COUNTER_MAX;
    assign READ_COUNTER_MAX = 4'b0101;
    assign WRITE_COUNTER_MAX = 4'b0101;

    //AXI memory
    logic [31:0]axi_araddr;
    logic [1:0]axi_arburst;
    logic [3:0]axi_arcache;
    logic [5:0]axi_arid;
    logic [7:0]axi_arlen;
    logic [0:0]axi_arlock;
    logic [2:0]axi_arprot;
    logic [3:0]axi_arqos;
    logic axi_arready;
    logic [3:0]axi_arregion;
    logic [2:0]axi_arsize;
    logic axi_arvalid;
    logic [31:0]axi_awaddr;
    logic [1:0]axi_awburst;
    logic [3:0]axi_awcache;
    logic [5:0]axi_awid;
    logic [7:0]axi_awlen;
    logic [0:0]axi_awlock;
    logic [2:0]axi_awprot;
    logic [3:0]axi_awqos;
    logic axi_awready;
    logic [3:0]axi_awregion;
    logic [2:0]axi_awsize;
    logic axi_awvalid;
    logic [5:0]axi_bid;
    logic axi_bready;
    logic [1:0]axi_bresp;
    logic axi_bvalid;
    logic [31:0]axi_rdata;
    logic [5:0]axi_rid;
    logic axi_rlast;
    logic axi_rready;
    logic [1:0]axi_rresp;
    logic axi_rvalid;
    logic [31:0]axi_wdata;
    logic axi_wlast;
    logic axi_wready;
    logic [3:0]axi_wstrb;
    logic axi_wvalid;
    logic [5:0]axi_wid;

    parameter SCRATCH_MEM_KB = 128;
    parameter MEM_LINES = (SCRATCH_MEM_KB*1024)/4;

    logic interrupt;
    logic timer_interrupt;

    assign interrupt = 0;

    axi_interface m_axi();
    //axi_interface ddr_axi();
    avalon_interface m_avalon();
    wishbone_interface dwishbone();

    trace_outputs_t tr;

    l2_requester_interface l2[L2_NUM_PORTS-1:0]();
    l2_memory_interface mem();

    local_memory_interface instruction_bram();
    local_memory_interface data_bram();

    //    assign m_axi.arready = bus_axi_arready;
    //    assign bus_axi_arvalid = m_axi.arvalid;
    //    assign bus_axi_araddr = m_axi.araddr;
    //
    //
    //    //read data
    //    assign bus_axi_rready = m_axi.rready;
    //    assign m_axi.rvalid = bus_axi_rvalid;
    //    assign m_axi.rdata = bus_axi_rdata;
    //    assign m_axi.rresp = bus_axi_rresp;
    //
    //    //Write channel
    //    //write address
    //    assign m_axi.awready = bus_axi_awready;
    //    assign bus_axi_awaddr = m_axi.awaddr;
    //    assign bus_axi_awvalid = m_axi.awvalid;
    //
    //
    //    //write data
    //    assign m_axi.wready = bus_axi_wready;
    //    assign bus_axi_wvalid = m_axi. wvalid;
    //    assign bus_axi_wdata = m_axi.wdata;
    //    assign bus_axi_wstrb = m_axi.wstrb;
    //
    //    //write response
    //    assign bus_axi_bready = m_axi.bready;
    //    assign m_axi.bvalid = bus_axi_bvalid;
    //    assign m_axi.bresp = bus_axi_bresp;

    assign l2[0].addr = addr;
    assign l2[0].be = be;
    assign l2[0].rnw = rnw;
    assign l2[0].is_amo = is_amo;
    assign l2[0].amo_type_or_burst_size = amo_type_or_burst_size;
    assign l2[0].sub_id = sub_id;

    assign l2[0].request_push = request_push;
    assign request_full = l2[0].request_full;

    assign inv_addr = l2[0].inv_addr;
    assign inv_valid = l2[0].inv_valid;
    assign l2[0].inv_ack = inv_ack;

    assign con_result = l2[0].con_result;
    assign con_valid = l2[0].con_valid;

    assign l2[0].wr_data = wr_data;
    assign l2[0].wr_data_push = wr_data_push;
    assign data_full = l2[0].data_full;

    assign rd_data = l2[0].rd_data;
    assign rd_sub_id = l2[0].rd_sub_id;
    assign rd_data_valid = l2[0].rd_data_valid;
    assign l2[0].rd_data_ack = rd_data_ack;


    assign l2[1].request_push = 0;
    assign l2[1].wr_data_push = 0;
    assign l2[1].inv_ack = l2[1].inv_valid;
    assign l2[1].rd_data_ack = l2[1].rd_data_valid;

    axi_to_arb l2_to_mem (.*, .l2(mem));
    l2_arbiter l2_arb (.*, .request(l2));

    ////////////////////////////////////////////////////
    //DDR AXI interface
    assign ddr_axi_araddr = axi_araddr;
    assign ddr_axi_arburst = axi_arburst;
    assign ddr_axi_arcache = axi_arcache;
    assign ddr_axi_arid = axi_arid;
    assign ddr_axi_arlen = axi_arlen;
    assign axi_arready = ddr_axi_arready;
    assign ddr_axi_arsize = axi_arsize;
    assign ddr_axi_arvalid = axi_arvalid;

    assign ddr_axi_awaddr = axi_awaddr;
    assign ddr_axi_awburst = axi_awburst;
    assign ddr_axi_awcache = axi_awcache;
    assign ddr_axi_awid = axi_awid;
    assign ddr_axi_awlen =  axi_awlen;
    assign axi_awready = ddr_axi_awready;
    assign ddr_axi_awvalid = axi_awvalid;
    
    assign axi_bid = ddr_axi_bid;
    assign ddr_axi_bready = axi_bready;
    assign axi_bresp = ddr_axi_bresp;
    assign axi_bvalid = ddr_axi_bvalid;

    assign axi_rdata = ddr_axi_rdata;
    assign axi_rid = ddr_axi_rid;
    assign axi_rlast = ddr_axi_rlast;
    assign ddr_axi_rready = axi_rready;
    assign axi_rresp = ddr_axi_rresp;
    assign axi_rvalid = ddr_axi_rvalid;

    assign ddr_axi_wdata = axi_wdata;
    assign ddr_axi_wlast = axi_wlast;
    assign axi_wready = ddr_axi_wready;
    assign ddr_axi_wstrb = axi_wstrb;
    assign ddr_axi_wvalid = axi_wvalid;


    ////////////////////////////////////////////////////
    //Trace Interface
    assign instruction_pc_dec = tr.instruction_pc_dec;
    assign instruction_data_dec = tr.instruction_data_dec;
    assign instruction_issued = tr.events.instruction_issued_dec;
    logic [$bits(cva5_trace_events_t)-1:0] cva5_events_packed;
    assign cva5_events_packed = tr.events;
    always_comb begin
        foreach(cva5_events_packed[i])
            cva5_events[$bits(cva5_trace_events_t)-1-i] = cva5_events_packed[i];
    end

endmodule
