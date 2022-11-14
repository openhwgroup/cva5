/*
 * Copyright © 2022 Eric Matthews,  Lesley Shannon
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

module l1_to_axi

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    import l2_config_and_types::*;

    (
        input logic clk,
        input logic rst,

        l2_requester_interface.slave cpu,
        axi_interface.master axi
    );

    localparam MAX_REQUESTS = 16;

    fifo_interface #(.DATA_WIDTH($bits(l2_request_t))) request_fifo ();
    fifo_interface #(.DATA_WIDTH(32)) data_fifo ();

    l2_request_t request_in;
    l2_request_t request;
    logic write_request;

    logic read_pop;
    logic write_pop;

    logic aw_complete;
    logic w_complete;
    logic aw_complete_r;
    logic w_complete_r;

    ////////////////////////////////////////////////////
    //Implementation
    assign cpu.request_full = request_fifo.full;
    assign cpu.data_full = data_fifo.full;

    //Repack input attributes
    assign request_in.addr = cpu.addr;
	assign request_in.be = cpu.be;
	assign request_in.rnw = cpu.rnw;
	assign request_in.is_amo = cpu.is_amo;
	assign request_in.amo_type_or_burst_size = cpu.amo_type_or_burst_size;
	assign request_in.sub_id = cpu.sub_id;

    assign request_fifo.push = cpu.request_push;
    assign request_fifo.potential_push = cpu.request_push;
    assign request_fifo.pop = read_pop | write_pop;
    assign request_fifo.data_in = request_in;
    assign request = request_fifo.data_out;

    assign data_fifo.push = cpu.wr_data_push;
    assign data_fifo.potential_push = cpu.wr_data_push;
    assign data_fifo.pop = write_pop;
    assign data_fifo.data_in = cpu.wr_data;

    cva5_fifo #(.DATA_WIDTH($bits(l2_request_t)), .FIFO_DEPTH(MAX_REQUESTS))
    request_fifo_block (
        .clk (clk), 
        .rst (rst), 
        .fifo (request_fifo)
    );
    cva5_fifo #(.DATA_WIDTH(32), .FIFO_DEPTH(MAX_REQUESTS))
    data_fifo_block (
        .clk (clk), 
        .rst (rst), 
        .fifo (data_fifo)
    );

    ////////////////////////////////////////////////////
    //AXI
    localparam MAX_WRITE_IN_FLIGHT = 64;
    logic [$clog2(MAX_WRITE_IN_FLIGHT)-1:0] write_in_flight_count;
    logic [$clog2(MAX_WRITE_IN_FLIGHT)-1:0] write_in_flight_count_next;

    logic [4:0] burst_size;
    assign burst_size = request.amo_type_or_burst_size;

    //Read Channel
    assign axi.arlen = 8'(burst_size);
    assign axi.arburst = (burst_size !=0) ? 2'b01 : '0;// INCR
    assign axi.rready = 1; //always ready to receive data
    assign axi.arsize = 3'b010;//4 bytes
    assign axi.arcache = 4'b0011; //Normal Non-cacheable Non-bufferable
    assign axi.arid = 6'(request.sub_id);

    assign axi.araddr = {request.addr, 2'b00} & {25'h1FFFFFF, ~burst_size, 2'b00};
    assign axi.arvalid = request.rnw & request_fifo.valid & ((request.sub_id[1:0] != L1_DCACHE_ID)  | ((request.sub_id[1:0] == L1_DCACHE_ID) & (write_in_flight_count == 0)));

    assign read_pop = axi.arvalid & axi.arready;

    //Write Channel
    assign axi.awlen = '0;
    assign axi.awburst = '0;//2'b01;// INCR
    assign axi.awsize = 3'b010;//4 bytes
    assign axi.bready = 1;
    assign axi.awcache = 4'b0011;//Normal Non-cacheable Non-bufferable
    assign axi.awaddr = {request.addr, 2'b00};
    assign axi.awid = 6'(request.sub_id);

    assign write_request = (~request.rnw) & request_fifo.valid & data_fifo.valid;
    assign axi.awvalid = write_request & ~aw_complete_r;

    assign axi.wdata = data_fifo.data_out;
    assign axi.wstrb = request.be;
    assign axi.wvalid = write_request & ~w_complete_r;
    assign axi.wlast = axi.wvalid;

    assign aw_complete = axi.awvalid & axi.awready;
    assign w_complete = axi.wvalid & axi.wready;

    always_ff @ (posedge clk) begin
        if (rst)
            aw_complete_r <= 0;
        else
            aw_complete_r <= (aw_complete_r | aw_complete) & ~write_pop;
    end
    always_ff @ (posedge clk) begin
        if (rst)
            w_complete_r <= 0;
        else
            w_complete_r <= (w_complete_r | w_complete) & ~write_pop;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            write_in_flight_count <= 0;
        else
            write_in_flight_count <= write_in_flight_count + $clog2(MAX_WRITE_IN_FLIGHT)'({(aw_complete | aw_complete_r) & (w_complete | w_complete_r)}) - $clog2(MAX_WRITE_IN_FLIGHT)'(axi.bvalid);
    end
    
    assign write_pop = (aw_complete | aw_complete_r) & (w_complete | w_complete_r);

    ////////////////////////////////////////////////////
    //Return Path
    //L1 always acks data, no need for rd_data_ack
    always_ff @ (posedge clk) begin
        cpu.rd_data <= axi.rdata;
        cpu.rd_data_valid <= axi.rvalid;
        cpu.rd_sub_id <= axi.rid[L2_SUB_ID_W-1:0];
    end
endmodule
