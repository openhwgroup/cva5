/*
 * Copyright © 2017-2019 Eric Matthews,  Lesley Shannon
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

module axi_to_arb

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    import l2_config_and_types::*;

    (
        input logic clk,
        input logic rst,

        //read addr channel
        input logic  axi_arready,
        output logic axi_arvalid,
        output logic[31:0] axi_araddr,
        output logic[7:0] axi_arlen,
        output logic[2:0] axi_arsize,
        output logic[1:0] axi_arburst,
        output logic[2:0] axi_arprot,
        output logic[3:0] axi_arcache,
        output logic[5:0] axi_arid,

        //read data channel
        output logic axi_rready,
        input logic axi_rvalid,
        input logic[31:0] axi_rdata,
        input logic[1:0] axi_rresp,
        input logic axi_rlast,
        input logic[5:0] axi_rid,

        //write addr channel
        input logic axi_awready,
        output logic axi_awvalid,
        output logic [31:0] axi_awaddr,
        output logic [7:0] axi_awlen,
        output logic [2:0] axi_awsize,
        output logic [1:0] axi_awburst,

        output logic[3:0] axi_awcache,
        output logic[2:0] axi_awprot,

        //write data
        input logic axi_wready,
        output logic axi_wvalid,
        output logic [31:0] axi_wdata,
        output logic [3:0] axi_wstrb,
        output logic axi_wlast,

        //write response
        output logic axi_bready,
        input logic axi_bvalid,
        input logic [1:0] axi_bresp,

        //arb interface
        l2_memory_interface.slave l2

    );

    logic pop_request;

    logic read_modify_write;
    logic read_modify_write_in_progress;
    logic address_phase_complete;
    logic [31:0] amo_result;
    logic [31:0] amo_result_r;
    logic [$clog2(EXAMPLE_CONFIG.DCACHE.LINE_W)-1:0] read_count;
    logic amo_write_ready;
    logic[4:0] write_reference_burst_count;

    amo_alu_inputs_t amo_alu_inputs;


    logic write_in_progress;
    logic write_transfer_complete;

    logic pop;

    logic[4:0] write_burst_count;
    logic[4:0] burst_count, burst_count_r;
    logic on_last_burst;


    //AMO read modify write support ****************************************************
    assign read_modify_write = l2.is_amo && (l2.amo_type_or_burst_size != AMO_LR_FN5 || l2.amo_type_or_burst_size != AMO_SC_FN5);

    always_ff @ (posedge clk) begin
        if (rst)
            read_modify_write_in_progress <= 0;
        else if (axi_bvalid)
            read_modify_write_in_progress <= 0;
        else if (l2.request_valid & read_modify_write)
            read_modify_write_in_progress <= 1;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            address_phase_complete <= 0;
        else if (pop)
            address_phase_complete <= 0;
        else if (axi_arvalid & axi_arready)
            address_phase_complete <= 1;
    end

    //TODO: if the data cache is made non-blocking on a miss then we could capture a previous request here instead of the one we just issued
    //safe under current circumstances as subsequent load won't be issued until the first one returns.
    always_ff @ (posedge clk) begin
        if (rst)
            read_count <= 0;
        else if (axi_rvalid && (axi_rid == 6'(l2.id)))
            read_count <= read_count + 1;
    end

    assign amo_alu_inputs.rs1_load = axi_rdata;
    assign amo_alu_inputs.rs2 = l2.wr_data;
    assign amo_alu_inputs.op = l2.amo_type_or_burst_size;

    amo_alu amo_unit (.*, .result(amo_result));

    //TODO:  assumption that all data caches have same line size, would have to update wrt the burst size to be safe if they have different line lengths
    //also update araddr
    always_ff @ (posedge clk) begin
        if (axi_rvalid && (read_count == l2.addr[$clog2(EXAMPLE_CONFIG.DCACHE.LINE_W)-1:0]))
            amo_result_r <= amo_result;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            amo_write_ready <= 0;
        else if (pop)
            amo_write_ready <= 0;
        else if (l2.is_amo && axi_rvalid && read_count == l2.addr[$clog2(EXAMPLE_CONFIG.DCACHE.LINE_W)-1:0])
            amo_write_ready <= 1;
    end
    //End AMO

    assign burst_count = l2.amo_type_or_burst_size;

    //read constants
    assign axi_arlen = 8'(burst_count); //
    assign axi_arburst = 2'b01;// INCR
    assign axi_rready = 1; //always ready to receive data
    assign axi_arsize = 3'b010;//4 bytes
    assign axi_arcache = 4'b0011; //bufferable cacheable memory
    assign axi_arprot = '0;
    assign axi_arid = 6'(l2.id);

    assign axi_araddr ={l2.addr[29:$clog2(EXAMPLE_CONFIG.DCACHE.LINE_W)],  {$clog2(EXAMPLE_CONFIG.DCACHE.LINE_W){1'b0}}, 2'b00};

    assign write_reference_burst_count = read_modify_write ? 0 : burst_count;

    //write constants
    assign axi_awlen = 8'(write_reference_burst_count);
    assign axi_awburst = 2'b01;// INCR
    assign axi_awsize = 3'b010;//4 bytes
    assign axi_bready = 1;
    assign axi_awcache = 4'b0011;//bufferable cacheable memory
    assign axi_awprot = '0;

    assign axi_awaddr ={l2.addr, 2'b00};

    assign axi_wdata = read_modify_write ? amo_result_r : l2.wr_data;

    assign axi_wstrb =read_modify_write ? '1 : l2.be;


    //Done when read request sent, or slave ack on write data
    assign pop = (axi_arvalid & axi_arready & ~read_modify_write) | (axi_awvalid & axi_awready);
    assign l2.request_pop = pop;

    //read channel
    always_ff @ (posedge clk) begin
        if (rst)
            axi_arvalid <= 0;
        else if (axi_arvalid & axi_arready)
            axi_arvalid <= 0;
        else if (l2.request_valid & l2.rnw & ~address_phase_complete)
            axi_arvalid <= 1;
    end

    //write channel
    always_ff @ (posedge clk) begin
        if (rst)
            axi_awvalid <= 0;
        else if (l2.wr_data_valid & l2.request_valid & (~l2.rnw | amo_write_ready) & ~write_in_progress)
            axi_awvalid <= 1;
        else if (axi_awready)
            axi_awvalid <= 0;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            write_in_progress <= 0;
        else if (axi_bvalid)
            write_in_progress <= 0;
        else if (l2.wr_data_valid & l2.request_valid & (~l2.rnw | amo_write_ready))
            write_in_progress <= 1;
    end


    always_ff @ (posedge clk) begin
        if (rst)
            write_burst_count <= 0;
        else if (axi_bvalid)
            write_burst_count <= 0;
        else if (axi_wvalid && axi_wready && write_reference_burst_count != write_burst_count)
            write_burst_count <= write_burst_count+1;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            on_last_burst <= 0;
        else if (axi_bvalid)
            on_last_burst <= 0;
        else if ((~write_in_progress && write_reference_burst_count == 0) ||  (write_in_progress && write_reference_burst_count == write_burst_count))
            on_last_burst <= 1;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            write_transfer_complete <= 0;
        else if (axi_bvalid)
            write_transfer_complete <= 0;
        else if (axi_wlast && axi_wready)
            write_transfer_complete <= 1;
    end


    assign axi_wvalid = write_in_progress & l2.wr_data_valid & ~write_transfer_complete;
    assign axi_wlast = on_last_burst & write_in_progress & l2.wr_data_valid & ~write_transfer_complete;

    assign l2.wr_data_read = write_in_progress & axi_wready & ~write_transfer_complete;


    //read response
    assign l2.rd_data = axi_rdata;
    assign l2.rd_id = axi_rid[L2_ID_W-1:0];
    assign l2.rd_data_valid = axi_rvalid;

endmodule

