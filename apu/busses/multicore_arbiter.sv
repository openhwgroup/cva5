/*
 * Copyright © 2024 Chris Keilbart
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module multicore_arbiter

    #(
        parameter int unsigned NUM_CORES = 1
    ) (
        input logic clk,
        input logic rst,

        mem_interface.mem_slave mems[NUM_CORES-1:0],

        //Requests can be returned out of order for different IDs
        //However, the original ordering of writes and reads to
        //the same address must be preserved
        input logic request_pop,
        output logic request_valid,
        output logic[31:2] request_addr,
        output logic request_rnw,
        output logic[4:0] request_rlen,
        output logic[31:0] request_wdata,
        output logic[3:0] request_wbe,
        output logic[1+$clog2(NUM_CORES):0] request_id,

        input logic request_rvalid,
        input logic[31:0] request_rdata,
        input logic[1+$clog2(NUM_CORES):0] request_rid,
        input logic[NUM_CORES-1:0] write_outstanding
    );

    //Multiplexes memory requests and submits invalidations
    //Write coalescing would be a nice future improvement
    localparam FIFO_DEPTH = 32;
    typedef logic[$clog2(FIFO_DEPTH):0] count_t;
    typedef logic[2+$clog2(NUM_CORES)-1:0] full_id_t;

    typedef struct packed {
        logic[31:2] addr;
        logic[4:0] rlen;
        logic rnw;
        logic[3:0] wbe;
        logic[31:0] wdata;
        full_id_t id;
        logic rmw;
    } request_t;
    request_t in_req;
    request_t out_req;
    fifo_interface #(.DATA_TYPE(request_t)) request_fifo();

    logic[NUM_CORES-1:0] requests;
    logic[NUM_CORES-1:0] acks;
    logic[NUM_CORES-1:0][31:2] addr;
    logic[NUM_CORES-1:0][4:0] rlen;
    logic[NUM_CORES-1:0] rnw;
    logic[NUM_CORES-1:0] rmw;
    logic[NUM_CORES-1:0][3:0] wbe;
    logic[NUM_CORES-1:0][31:0] wdata;
    logic[NUM_CORES-1:0][1:0] id;
    full_id_t padded_id;
    logic[NUM_CORES-1:0] rvalids;
    logic[(NUM_CORES == 1 ? 1 : $clog2(NUM_CORES))-1:0] chosen_port;
    logic rvalid;
    logic[31:0] rdata;
    full_id_t rid;
    logic[NUM_CORES-1:0] out_core;
    count_t[NUM_CORES-1:0] wcounts;
    
    logic request_push;
    logic request_finished;

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation
    
    //Unpack interface
    generate for (i = 0; i < NUM_CORES; i++) begin : gen_unpack
        assign requests[i] = mems[i].request;
        assign addr[i] = mems[i].addr;
        assign rlen[i] = mems[i].rlen;
        assign rnw[i] = mems[i].rnw;
        assign rmw[i] = mems[i].rmw;
        assign wbe[i] = mems[i].wbe;
        assign wdata[i] = mems[i].wdata;
        assign id[i] = mems[i].id;
        assign acks[i] = request_push & i == int'(chosen_port);
        assign mems[i].ack = acks[i];
        assign mems[i].inv_addr = in_req.addr;
        assign mems[i].inv = request_push & ~in_req.rnw & i != int'(chosen_port);
        assign mems[i].rvalid = rvalids[i];
        assign mems[i].rdata = request_rdata;
        assign mems[i].rid = request_rid[1:0];
        assign mems[i].write_outstanding = wcounts[i][$clog2(FIFO_DEPTH)] | write_outstanding[i];
    end endgenerate
    
    //Once accepted, stall until the RMW is resolved
    logic[(NUM_CORES == 1 ? 1 : $clog2(NUM_CORES))-1:0] rmw_index;
    logic rmw_is_on;
    logic[NUM_CORES-1:0] accept_request_from_rmw_core;
    logic rmw_hit;

    always_ff @(posedge clk) begin
        if (in_req.rmw & request_push)
            rmw_index <= chosen_port;
    end

    always_ff @(posedge clk) begin
        if (rst)
            rmw_is_on <= 0;
        else if (in_req.rmw & request_push)
            rmw_is_on <= 1;
        else if (~in_req.rmw)
            rmw_is_on <= 0;
    end

    assign accept_request_from_rmw_core = (rmw_is_on ? (1'b1 << rmw_index) : {NUM_CORES{1'b1}});
    assign rmw_hit = |(requests & accept_request_from_rmw_core);

    //Request FIFO
    assign request_push = ~request_fifo.full & |requests & (~rmw_is_on | rmw_hit);
    assign request_fifo.data_in = in_req;
    assign out_req = request_fifo.data_out;
    assign request_valid = request_fifo.valid;
    assign request_addr = out_req.addr;
    assign request_rnw = out_req.rnw;
    assign request_rlen = out_req.rlen;
    assign request_wdata = out_req.wdata;
    assign request_wbe = out_req.wbe;
    assign request_id = out_req.id;

    assign request_fifo.push = request_push;
    assign request_fifo.potential_push = request_push;
    assign request_fifo.pop = request_pop;
    cva5_fifo #(.DATA_TYPE(request_t), .FIFO_DEPTH(FIFO_DEPTH)) fifo_inst (.fifo(request_fifo), .*);

    //Arbitration
    round_robin #(.NUM_PORTS(NUM_CORES)) rr (
        .requests(requests & accept_request_from_rmw_core),
        .grant(request_push),
        .grantee(chosen_port),
    .*);

    //Select input
    assign in_req = '{
        addr : addr[chosen_port],
        rlen : rlen[chosen_port],
        rnw : rnw[chosen_port],
        wbe : wbe[chosen_port],
        wdata : wdata[chosen_port],
        id : padded_id,
        rmw : rmw[chosen_port]
    };

    generate if (NUM_CORES == 1) begin : gen_no_id
        assign padded_id = id[chosen_port];
        assign rvalids[0] = request_rvalid;
        assign out_core[0] = 1;
    end else begin : gen_id
        assign padded_id = {chosen_port, id[chosen_port]};
        assign rvalids = request_rvalid << request_rid[2+:$clog2(NUM_CORES)];
        assign out_core = 1 << request_id[2+:$clog2(NUM_CORES)];
    end endgenerate

    //Write tracking; tracked for each core
    logic[NUM_CORES-1:0] wcount_incr;
    logic[NUM_CORES-1:0] wcount_decr;

    always_comb begin
        for (int j = 0; j < NUM_CORES; j++) begin
            wcount_incr[j] = acks[j] & ~rnw[j];
            wcount_decr[j] = out_core[j] & ~request_rnw & request_pop;
        end
    end

    always_ff @(posedge clk) begin
        if (rst)
            wcounts <= '0;
        else begin
            for (int j = 0; j < NUM_CORES; j++) //Flipped increment / decrement allows the MSB to be used as a nonzero signal
                wcounts[j] <= wcounts[j] - count_t'(wcount_incr[j]) + count_t'(wcount_decr[j]);
        end
    end

endmodule
