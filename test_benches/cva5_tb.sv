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

`timescale 1ns/1ns

`define  MEMORY_FILE  "/home/ematthew/Research/RISCV/software/riscv-tools/riscv-tests/benchmarks/dhrystone.riscv.sim_init"
`define  UART_LOG  "/home/ematthew/uart.log"

module cva5_tb 

    import tb_tools::*;
    import cva5_config::*;
    import l2_config_and_types::*;
    import riscv_types::*;
    import cva5_types::*;

  ( );

    logic simulator_clk;
    logic simulator_resetn;

    //axi block diagram inputs
    logic axi_clk;
    logic resetn;
    logic sin;

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


    axi_interface ddr_axi();

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


    //AXI bus
    logic ACLK;
    logic [12:0]bus_axi_araddr;
    logic bus_axi_arready;
    logic bus_axi_arvalid;
    logic [12:0]bus_axi_awaddr;
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

    //axi block diagram outputs
    logic processor_reset;
    logic processor_clk;
    logic sout;

    logic clk;
    logic rst;


    //*****************************

    assign axi_clk = simulator_clk;
    assign resetn = simulator_resetn;

    assign clk = simulator_clk;
    assign rst = processor_reset;

    local_memory_interface instruction_bram();
    local_memory_interface data_bram();

    axi_interface m_axi();
    avalon_interface m_avalon();
    wishbone_interface dwishbone();

    l2_requester_interface l2[L2_NUM_PORTS-1:0]();
    l2_memory_interface mem();


    logic interrupt;
    logic timer_interrupt;

    logic[31:0] dec_pc_debug;
    logic[31:0] if2_pc_debug;

    integer output_file;

    assign l2[1].request = 0;
    assign l2[1].request_push = 0;
    assign l2[1].wr_data_push = 0;
    assign l2[1].inv_ack = l2[1].inv_valid;
    assign l2[1].rd_data_ack = l2[1].rd_data_valid;

    sim_mem simulation_mem = new();


    //RAM Block
    always_ff @(posedge processor_clk) begin
      if (instruction_bram.en) begin
        instruction_bram.data_out <= simulation_mem.readw(instruction_bram.addr);
        simulation_mem.writew(instruction_bram.addr,instruction_bram.data_in, instruction_bram.be);
      end
      else begin
        instruction_bram.data_out <= 0;
      end
    end

    always_ff @(posedge processor_clk) begin
      if (data_bram.en) begin
        data_bram.data_out <= simulation_mem.readw(data_bram.addr);
        simulation_mem.writew(data_bram.addr,data_bram.data_in, data_bram.be);
      end
      else begin
        data_bram.data_out <= 0;
      end
    end

    cva5 uut (.*, .l2(l2[0]));

    design_2 infra(.*);

    l2_arbiter l2_arb (.*, .request(l2));

    axi_to_arb l2_to_mem (.*, .l2(mem));

    axi_mem_sim #(`MEMORY_FILE) ddr_interface (.*, .axi(ddr_axi), .if_pc(if2_pc_debug), .dec_pc(dec_pc_debug));

    always
        #1 simulator_clk = ~simulator_clk;

    initial begin
        simulator_clk = 0;
        interrupt = 0;
        timer_interrupt = 0;
        simulator_resetn = 0;

        simulation_mem.load_program(`MEMORY_FILE, RESET_VEC);

        output_file = $fopen(`UART_LOG, "w");
        if (output_file == 0) begin
            $error ("couldn't open log file");
            $finish;
        end
        do_reset();

        #1800000;
        $fclose(output_file);
        $finish;
    end

    task do_reset;
    begin
        simulator_resetn = 1'b0;
        #500 simulator_resetn = 1'b1;
    end
    endtask


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







    assign ddr_axi.araddr = mem_axi_araddr;
    assign ddr_axi.arburst = mem_axi_arburst;
    assign ddr_axi.arcache = mem_axi_arcache;
    assign ddr_axi.arid = mem_axi_arid;
    assign ddr_axi.arlen = mem_axi_arlen;
    assign mem_axi_arready = ddr_axi.arready;
    assign ddr_axi.arsize = mem_axi_arsize;
    assign ddr_axi.arvalid = mem_axi_arvalid;

    assign ddr_axi.awaddr = mem_axi_awaddr;
    assign ddr_axi.awburst = mem_axi_awburst;
    assign ddr_axi.awcache = mem_axi_awcache;
    assign ddr_axi.awid = mem_axi_awid;
    assign ddr_axi.awlen = mem_axi_awlen;
    assign mem_axi_awready = ddr_axi.awready;
    assign ddr_axi.awvalid = mem_axi_awvalid;

    assign mem_axi_bid = ddr_axi.bid;
    assign ddr_axi.bready = mem_axi_bready;
    assign mem_axi_bresp = ddr_axi.bresp;
    assign mem_axi_bvalid = ddr_axi.bvalid;

    assign mem_axi_rdata = ddr_axi.rdata;
    assign mem_axi_rid = ddr_axi.rid;
    assign mem_axi_rlast = ddr_axi.rlast;
    assign ddr_axi.rready = mem_axi_rready;
    assign mem_axi_rresp = ddr_axi.rresp;
    assign mem_axi_rvalid = ddr_axi.rvalid;

    assign ddr_axi.wdata = mem_axi_wdata;
    assign ddr_axi.wlast = mem_axi_wlast;
    assign mem_axi_wready = ddr_axi.wready;
    assign ddr_axi.wstrb = mem_axi_wstrb;
    assign ddr_axi.wvalid = mem_axi_wvalid;


    //Capture writes to UART
    always_ff @(posedge processor_clk) begin
      if (m_axi.wvalid && bus_axi_wready && m_axi.awaddr[13:0] == 4096) begin
            $fwrite(output_file, "%c",m_axi.wdata[7:0]);
      end
    end


    assign sin = 0;

endmodule
