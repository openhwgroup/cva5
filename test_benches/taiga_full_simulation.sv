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

import tb_tools::*;
import taiga_config::*;
import taiga_types::*;
import l2_config_and_types::*;

`define  MEMORY_FILE "/home/ematthew/Research/RISCV/software/riscv-tools/riscv-tests/benchmarks/dhrystone.riscv.sim_init" //change this to appropriate location "/home/ematthew/Downloads/dhrystone.riscv.sim_init"
`define  UART_LOG  "/home/ematthew/uart.log" //change this to appropriate location

module taiga_full_simulation ();
    logic [3:0] WRITE_COUNTER_MAX;
    logic [3:0] READ_COUNTER_MAX;
    assign READ_COUNTER_MAX = 4'b0101;
    assign WRITE_COUNTER_MAX = 4'b0101;

    logic simulator_clk;
    logic simulator_resetn;
    logic peripheral_resetn;
    logic interconnect_resetn;
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

    //axi block diagram outputs
    logic processor_reset;
    logic processor_clk;
    logic sout;

    logic clk;
    logic rst;


    //*****************************

    assign axi_clk = simulator_clk;
    assign processor_clk = simulator_clk;
    assign resetn = simulator_resetn;

    assign clk = simulator_clk;
    assign rst = processor_reset;

    local_memory_interface instruction_bram();
    local_memory_interface data_bram();

    axi_interface m_axi();
    avalon_interface m_avalon();

    l2_requester_interface l2[L2_NUM_PORTS-1:0]();
    l2_memory_interface mem();


    logic interrupt;
    logic timer_interrupt;

    logic[31:0] dec_pc_debug;
    logic[31:0] if2_pc_debug;
    logic dec_advance_debug;

    logic[31:0] dec_instruction2;
    logic[31:0] dec_instruction;


    integer output_file;
    integer output_file2;

    assign l2[1].request = 0;
    assign l2[1].request_push = 0;
    assign l2[1].wr_data_push = 0;
    assign l2[1].inv_ack = l2[1].inv_valid;
    assign l2[1].rd_data_ack = l2[1].rd_data_valid;

    sim_mem simulation_mem = new();


    //RAM Block
    assign instruction_bram.data_in = '0;
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

    taiga uut (.*, .l2(l2[0]));

    //design_2 infra(.*);

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

        output_file2 = $fopen("/home/ematthew/trace", "w");
        if (output_file2 == 0) begin
            $error ("couldn't open log file");
            $finish;
        end

        do_reset();

        //#1200000;
        //$fclose(output_file);
        //$fclose(output_file2);

        //$finish;
    end

    assign dec_instruction2 = simulation_mem.readw(dec_pc_debug[31:2]);

    always_ff @(posedge simulator_clk) begin
        //addi r0 r0 1
        if (dec_instruction2 == 32'h00100013) begin
            $fclose(output_file);
            $fclose(output_file2);
            $finish;
        end
    end


    task do_reset;
    begin
        interconnect_resetn = 1'b0;
        #100 interconnect_resetn = 1'b1;
        peripheral_resetn = 1'b0;
        #100 peripheral_resetn = 1'b1;
        processor_reset = 1'b1;
         #100 processor_reset = 1'b0;
    end
    endtask

     //read channel
    logic[3:0] read_counter;
    logic begin_read_counter;

    always_ff @(posedge simulator_clk) begin
        if (!peripheral_resetn) begin
            m_axi.rvalid <= 0;
            m_axi.arready <= 1; //You want it to start at ready
            m_axi.rresp <= 0;
            read_counter <= READ_COUNTER_MAX;
        end
        else begin
            if(m_axi.arready == 1 && m_axi.arvalid == 1) begin
                m_axi.arready <= 0;
                begin_read_counter <= 1;
                m_axi.rdata <= 32'hFFFFFF21;
            end

            if(begin_read_counter) begin
                if(read_counter == 0) begin
                   m_axi.rvalid <= 1;
                   m_axi.arready <= 1;
                   read_counter <= READ_COUNTER_MAX;
                   begin_read_counter <= 0;
               end
                else begin
                   read_counter <= read_counter - 1;
                   m_axi.rvalid <= 0;
                end
            end

            if(m_axi.rvalid &&  m_axi.rready) begin
                m_axi.rvalid <= 0;
            end

        end
    end

    //Write channel
    //write address
    logic[3:0] write_counter;
    logic begin_write_counter;

    always_ff @(posedge simulator_clk) begin
        if (!peripheral_resetn) begin
            m_axi.wready <= 0;
            m_axi.awready <= 1; //You want it to start at ready
            m_axi.bresp <= 0;
            write_counter <= WRITE_COUNTER_MAX;
        end
        else begin
            if(m_axi.awready == 1 && m_axi.awvalid == 1) begin
                m_axi.awready <= 0;
                begin_write_counter <= 1;
            end

            if(begin_write_counter) begin
                if(write_counter == 0) begin
                   m_axi.awready <= 1;
                   m_axi.wready <= 1;
                   write_counter <= WRITE_COUNTER_MAX;
                   begin_write_counter <= 0;
               end
                else begin
                   write_counter <= write_counter - 1;
                   m_axi.wready <= 0;
                end
            end

            if(m_axi.bready == 1 && m_axi.wready) begin
                m_axi.bvalid <= 1;
                m_axi.bresp = 0;
            end
            else begin
                m_axi.bvalid <= 0;
                m_axi.bresp = 0;
            end

            if(m_axi.wready & m_axi.wvalid) begin
                m_axi.wready <= 0;
            end
        end
    end

    assign ddr_axi.araddr = axi_araddr;
    assign ddr_axi.arburst = axi_arburst;
    assign ddr_axi.arcache = axi_arcache;
    assign ddr_axi.arid = axi_arid;
    assign ddr_axi.arlen = {4'b0, axi_arlen[3:0]};
    assign  axi_arready = ddr_axi.arready;
    assign ddr_axi.arsize = axi_arsize;
    assign ddr_axi.arvalid = axi_arvalid;

    assign ddr_axi.awaddr = axi_awaddr;
    assign ddr_axi.awburst = axi_awburst;
    assign ddr_axi.awcache = axi_awcache;
    assign ddr_axi.awid = axi_awid;
    assign ddr_axi.awlen = axi_awlen;
    assign axi_awready = ddr_axi.awready;
    assign ddr_axi.awvalid = axi_awvalid;

    assign axi_bid = ddr_axi.bid;
    assign ddr_axi.bready = axi_bready;
    assign axi_bresp = ddr_axi.bresp;
    assign axi_bvalid = ddr_axi.bvalid;

    assign axi_rdata = ddr_axi.rdata;
    assign axi_rid = ddr_axi.rid;
    assign axi_rlast = ddr_axi.rlast;
    assign ddr_axi.rready = axi_rready;
    assign axi_rresp = ddr_axi.rresp;
    assign axi_rvalid = ddr_axi.rvalid;

    assign ddr_axi.wdata = axi_wdata;
    assign ddr_axi.wlast = axi_wlast;
    assign axi_wready = ddr_axi.wready;
    assign ddr_axi.wstrb = axi_wstrb;
    assign ddr_axi.wvalid = axi_wvalid;


    //Capture writes to UART
    always_ff @(posedge simulator_clk) begin
      //if (m_axi.awready && m_axi.awaddr[13:0] == 4096) begin
      if (m_axi.wvalid && m_axi.wready && m_axi.awaddr[13:0] == 4096) begin
            $fwrite(output_file, "%c",m_axi.wdata[7:0]);
      end
    end


    assign sin = 0;



    ////////////////////////////////////////////////////

    always_ff @(posedge clk) begin
       if (dec_advance_debug) begin
            $fwrite(output_file2, simulation_mem.readopcode(instruction_bram.addr));
            $fwrite(output_file2, "\n");
       end
    end



endmodule
