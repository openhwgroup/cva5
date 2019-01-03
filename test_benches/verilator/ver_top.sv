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

import taiga_config::*;
import taiga_types::*;
import l2_config_and_types::*;


module ver_top # (
        parameter MEMORY_FILE = "/home/ematthew/Research/RISCV/software/riscv-tools/riscv-tests/benchmarks/dhrystone.riscv.hw_init" //change this to appropriate location "/home/ematthew/Downloads/dhrystone.riscv.sim_init"
        )
        (
        input logic clk,
        input logic rst,

        //        //AXI bus
        //        output logic [31:0]bus_axi_araddr,
        //        output logic [1:0]bus_axi_arburst,
        //        output logic [3:0]bus_axi_arcache,
        //        output logic [5:0]bus_axi_arid,
        //        output logic [7:0]bus_axi_arlen,
        //        output logic [0:0]bus_axi_arlock,
        //        output logic [2:0]bus_axi_arprot,
        //        output logic [3:0]bus_axi_arqos,
        //        input logic bus_axi_arready,
        //        output logic [3:0]bus_axi_arregion,
        //        output logic [2:0]bus_axi_arsize,
        //        output logic bus_axi_arvalid,
        //        output logic [31:0]bus_axi_awaddr,
        //        output logic [1:0]bus_axi_awburst,
        //        output logic [3:0]bus_axi_awcache,
        //        output logic [5:0]bus_axi_awid,
        //        output logic [7:0]bus_axi_awlen,
        //        output logic [0:0]bus_axi_awlock,
        //        output logic [2:0]bus_axi_awprot,
        //        output logic [3:0]bus_axi_awqos,
        //        input logic bus_axi_awready,
        //        output logic [3:0]bus_axi_awregion,
        //        output logic [2:0]bus_axi_awsize,
        //        output logic bus_axi_awvalid,
        //        output logic [5:0]bus_axi_bid,
        //        output logic bus_axi_bready,
        //        input logic [1:0]bus_axi_bresp,
        //        input logic bus_axi_bvalid,
        //        input logic [31:0]bus_axi_rdata,
        //        output logic [5:0]bus_axi_rid,
        //        output logic bus_axi_rlast,
        //        output logic bus_axi_rready,
        //        input logic [1:0]bus_axi_rresp,
        //        input logic bus_axi_rvalid,
        //        output logic [31:0]bus_axi_wdata,
        //        output logic bus_axi_wlast,
        //        input logic bus_axi_wready,
        //        output logic [3:0]bus_axi_wstrb,
        //        output logic bus_axi_wvalid,
        //        output logic [5:0]bus_axi_wid,

        output logic write_uart,
        output logic [7:0] uart_byte,
        output logic [31:0] dec_instruction_r,
        output logic [31:0] dec_pc_debug_r,

        //L2
        //l2 request
        output logic [29:0] addr,
        output logic [3:0] be,
        output logic rnw,
        output logic is_amo,
        output logic [4:0] amo_type_or_burst_size,
        output logic [L2_SUB_ID_W-1:0] sub_id,

        output logic request_push,
        input logic request_full,

        input logic [31:2] inv_addr,
        input logic inv_valid,
        output logic inv_ack,

        input logic con_result,
        input logic con_valid,

        output logic [31:0] wr_data,
        output logic wr_data_push,
        input logic data_full,

        input logic [31:0] rd_data,
        input logic [L2_SUB_ID_W-1:0] rd_sub_id,
        input logic rd_data_valid,
        output logic rd_data_ack
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

    logic [31:0] dec_instruction;
    logic [31:0] dec_pc_debug;

    parameter SCRATCH_MEM_KB = 16;
    parameter MEM_LINES = (SCRATCH_MEM_KB*1024)/4;

    logic [31:0] if2_pc_debug;
    logic interrupt;
    logic timer_interrupt;
    logic dec_advance_debug;

    assign interrupt = 0;

    axi_interface m_axi();
    avalon_interface m_avalon();
    l2_requester_interface l2[L2_NUM_PORTS-1:0]();
    l2_memory_interface mem();


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



    local_memory_interface instruction_bram();
    local_memory_interface data_bram();


    byte_en_BRAM #(MEM_LINES, MEMORY_FILE, 1) inst_data_ram (
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


    taiga cpu(.*, .l2(l2[0]));

   // always_ff @(posedge clk) begin
     //   dec_instruction_r <= dec_instruction;
    //    dec_pc_debug_r <= dec_pc_debug;
    //end

    //read channel
    logic[3:0] read_counter;
    logic begin_read_counter;

    always_ff @(posedge clk) begin
        if (rst) begin
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

    always_ff @(posedge clk) begin
        if (rst) begin
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
                m_axi.bresp <= 0;
            end
            else begin
                m_axi.bvalid <= 0;
                m_axi.bresp <= 0;
            end

            if(m_axi.wready & m_axi.wvalid) begin
                m_axi.wready <= 0;
            end
        end
    end

    initial begin
        write_uart = 0;
        uart_byte = 0;
    end
    //Capture writes to UART
    always_ff @(posedge clk) begin
        write_uart <= (m_axi.wvalid && m_axi.wready && m_axi.awaddr[13:0] == 4096);
        uart_byte <= m_axi.wdata[7:0];
    end

endmodule
