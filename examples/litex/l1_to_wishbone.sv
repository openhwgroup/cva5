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

module l1_to_wishbone

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    import l2_config_and_types::*;

    (
        input logic clk,
        input logic rst,

        l2_requester_interface.slave cpu,
        wishbone_interface.master wishbone
    );

    localparam MAX_REQUESTS = 32;

    fifo_interface #(.DATA_WIDTH($bits(l2_request_t))) request_fifo ();
    fifo_interface #(.DATA_WIDTH(32)) data_fifo ();

    l2_request_t request_in;
    l2_request_t request;

    logic request_complete;
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
    assign request_fifo.pop = request_complete;
    assign request_fifo.data_in = request_in;
    assign request = request_fifo.data_out;

    assign data_fifo.push = cpu.wr_data_push;
    assign data_fifo.potential_push = cpu.wr_data_push;
    assign data_fifo.pop = wishbone.we & wishbone.ack;
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
    //Wishbone
    logic [4:0] burst_size;
    logic [4:0] burst_count;
    assign wishbone.cti = 0;
    assign wishbone.bte = 0;

    always_ff @ (posedge clk) begin
        if (rst | request_fifo.pop)
            burst_count <= 0;
        else
            burst_count <= burst_count + 5'(wishbone.ack);
    end

    assign burst_size = request.amo_type_or_burst_size;
    assign request_complete = wishbone.ack & (burst_count == burst_size);

    assign wishbone.adr[29:5] = request.addr[29:5];
    assign wishbone.adr[4:0] = (request.addr[4:0] & ~burst_size) | (burst_count & burst_size);
    assign wishbone.sel = request.rnw ? '1 : request.be;
    assign wishbone.we = ~request.rnw;

    assign wishbone.dat_w = data_fifo.data_out;

    assign wishbone.stb = request_fifo.valid;
    assign wishbone.cyc = request_fifo.valid;

    ////////////////////////////////////////////////////
    //Return Path
    //L1 always acks data, no need for rd_data_ack
    always_ff @ (posedge clk) begin
        cpu.rd_data <= wishbone.dat_r;
        cpu.rd_data_valid <= request.rnw & wishbone.ack;
        cpu.rd_sub_id <= request.sub_id;
    end

endmodule
