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

module axi_adapter

    #(
        parameter int unsigned NUM_CORES = 1
    ) (
        input logic clk,
        input logic rst,

        mem_interface.mem_slave mems[NUM_CORES-1:0],
        axi_interface.master axi
    );

    localparam MAX_OUTSTANDING = 8;
    localparam MAX_W = $clog2(MAX_OUTSTANDING);

    typedef logic[7:0] hash_t;
    typedef logic[MAX_W:0] count_t;
    typedef logic[MAX_W-1:0] index_t;

    ////////////////////////////////////////////////////
    //Multicore interface
    //Arbitrates requests
    logic request_pop;
    logic request_valid;
    logic[31:2] request_addr;
    logic request_rnw;
    logic[4:0] request_rlen;
    logic[31:0] request_wdata;
    logic[3:0] request_wbe;
    logic[1+$clog2(NUM_CORES):0] request_id;
    logic request_rvalid;
    logic[31:0] request_rdata;
    logic[1+$clog2(NUM_CORES):0] request_rid;
    logic[NUM_CORES-1:0] write_outstanding;

    multicore_arbiter #(.NUM_CORES(NUM_CORES)) arb (
        .mems(mems),
        .request_pop(request_pop),
        .request_valid(request_valid),
        .request_addr(request_addr),
        .request_rnw(request_rnw),
        .request_rlen(request_rlen),
        .request_wdata(request_wdata),
        .request_wbe(request_wbe),
        .request_id(request_id),
        .request_rvalid(request_rvalid),
        .request_rdata(request_rdata),
        .request_rid(request_rid),
        .write_outstanding(write_outstanding),
    .*);

    ////////////////////////////////////////////////////
    //AXI interface
    //Read bursts and single writes
    //Ordering between reads and writes must be enforced
    logic addr_blocked;

    //AR
    assign axi.arvalid = request_valid & request_rnw & ~addr_blocked;
    assign axi.araddr = {request_addr[31:7], request_addr[6:2] & ~request_rlen, 2'b00};
    assign axi.arlen = {3'b0, request_rlen};
    assign axi.arsize = 3'b010; //4 bytes
    assign axi.arburst = 2'b01; //Incrementing
    assign axi.arcache = 4'b0011; //Bufferable and non-cacheable memory
    assign axi.arlock = 0; //Not locked

    //R
    assign axi.rready = 1;
    assign request_rdata = axi.rdata;
    assign request_rvalid = axi.rvalid;
    //Don't care about rresp or rlast

    logic sent_aw;
    logic sent_w;
    logic write_sent;
    assign write_sent = (axi.awvalid & axi.awready | sent_aw) & (axi.wvalid & axi.wready | sent_w);

    always_ff @(posedge clk) begin
        if (rst | write_sent) begin
            sent_aw <= 0;
            sent_w <= 0;
        end
        else begin
            sent_aw <= sent_aw | (axi.awvalid & axi.awready);
            sent_w <= sent_w | (axi.wvalid & axi.wready);
        end
    end

    //AW
    assign axi.awvalid = request_valid & ~request_rnw & ~sent_aw & ~addr_blocked;
    assign axi.awaddr = {request_addr, 2'b00};
    assign axi.awlen = '0;
    assign axi.awsize = 3'b010; //4 bytes
    assign axi.awburst = 2'b01; //Incrementing
    assign axi.awcache = 4'b0011; //Bufferable and non-cacheable memory
    assign axi.awlock = 0; //Not locked

    //W
    assign axi.wvalid = request_valid & ~request_rnw & ~sent_w;
    assign axi.wdata = request_wdata;
    assign axi.wstrb = request_wbe;
    assign axi.wlast = 1;

    //B
    assign axi.bready = 1;
    //Don't care about bresp

    assign request_pop = (axi.arvalid & axi.arready) | write_sent;

    ////////////////////////////////////////////////////
    //Outstanding tracking
    //Outstanding requests are tracked using a fully-associative array
    
    //Writes need to wait for outstanding write collisions to finish
    //Writes need to wait for outstanding read collisions to finish
    //Reads need to wait for outstanding write collisions to finish

    //Free slots
    logic[MAX_OUTSTANDING-1:0] frees;
    index_t free_index;

    priority_encoder #(.WIDTH(MAX_OUTSTANDING)) free_enc (
        .priority_vector(frees),
        .encoded_result(free_index)
    );

    always_ff @(posedge clk) begin
        if (rst)
            frees <= '1;
        else begin
            if (axi.rvalid & axi.rlast)
                frees[axi.rid[MAX_W-1:0]] <= 1;
            if (axi.bvalid)
                frees[axi.bid[MAX_W-1:0]] <= 1;
            if ((axi.awvalid & axi.awready) | (axi.arvalid & axi.arready))
                frees[free_index] <= 0;
        end
    end

    always_comb begin
        axi.arid = '0;
        axi.awid = '0;
        axi.arid[MAX_W-1:0] = free_index;
        axi.awid[MAX_W-1:0] = free_index;
    end

    //Outstanding storage
    hash_t request_hash;
    logic[5:0] request_lower;
    logic[5:0] request_upper;

    hash_t[MAX_OUTSTANDING-1:0] hashes;
    logic[MAX_OUTSTANDING-1:0] rnws;
    logic[MAX_OUTSTANDING-1:0][5:0] lowers;
    logic[MAX_OUTSTANDING-1:0][5:0] uppers;
    logic[MAX_OUTSTANDING-1:0][3:0] wbes;
    logic[MAX_OUTSTANDING-1:0][1+$clog2(NUM_CORES):0] ids;
    
    always_ff @(posedge clk) begin
        if ((axi.awvalid & axi.awready) | (axi.arvalid & axi.arready)) begin
            rnws[free_index] <= request_rnw;
            lowers[free_index] <= request_lower;
            uppers[free_index] <= request_upper;
            wbes[free_index] <= request_wbe;
            ids[free_index] <= request_id;
            hashes[free_index] <= request_hash;
        end
    end

    ////////////////////////////////////////////////////
    //Hash function
    //8-bit hashes can easily be compared using the carry circuitry
    //Only hash address bits that do not correspond to a line
    assign request_hash[0] = request_addr[8] ^ request_addr[16] ^ request_addr[24];
    assign request_hash[1] = request_addr[9] ^ request_addr[17] ^ request_addr[25];
    assign request_hash[2] = request_addr[10] ^ request_addr[18] ^ request_addr[26];
    assign request_hash[3] = request_addr[11] ^ request_addr[19] ^ request_addr[27];
    assign request_hash[4] = request_addr[12] ^ request_addr[20] ^ request_addr[28];
    assign request_hash[5] = request_addr[13] ^ request_addr[21] ^ request_addr[29];
    assign request_hash[6] = request_addr[14] ^ request_addr[22] ^ request_addr[30];
    assign request_hash[7] = request_addr[15] ^ request_addr[23] ^ request_addr[31];

    ////////////////////////////////////////////////////
    //Collision check
    //Collisions are checked at byte granularity; this is complicated by burst requests
    //Therefore, the lower and upper boundaries of the request within a 64-byte "arena" are stored
    //Collisions must therefore be within the boundaries
    //Writes collide with all outstanding requests
    //Reads only collide with outstanding writes
    logic[MAX_OUTSTANDING-1:0] range_collision;
    logic[MAX_OUTSTANDING-1:0] wbe_collision;
    logic[MAX_OUTSTANDING-1:0] hash_collision;
    always_comb begin
        for (int i = 0; i < MAX_OUTSTANDING; i++) begin
            hash_collision[i] = ~frees[i] & request_hash == hashes[i];
            if (request_rnw) begin
                range_collision[i] = (axi.araddr[7:2] <= lowers[i]) & (axi.araddr[7:2] + {1'b0, request_rlen} >= uppers[i]);
                wbe_collision[i] = ~rnws[i];
            end
            else begin
                range_collision[i] = (request_addr[7:2] >= lowers[i]) & (request_addr[7:2] <= uppers[i]);
                wbe_collision[i] = rnws[i] | |(request_wbe & wbes[i]);
            end
        end
    end
    assign addr_blocked = |(hash_collision & range_collision & wbe_collision) | ~|frees;

    assign request_lower = request_rnw ? axi.araddr[7:2] : request_addr[7:2];
    assign request_upper = request_rnw ? axi.araddr[7:2] + {1'b0, request_rlen} : request_addr[7:2];

    assign request_rid = ids[axi.rid[MAX_W-1:0]];

    //Write outstanding check
    logic[NUM_CORES-1:0][MAX_OUTSTANDING-1:0] outstanding_is_core;
    always_comb begin
        write_outstanding = '0;
        for (int i = 0; i < NUM_CORES; i++) begin
            for (int j = 0; j < MAX_OUTSTANDING; j++)
                write_outstanding[i] |= ~frees[j] & ~rnws[j] & outstanding_is_core[i][j];
        end
    end

    generate if (NUM_CORES > 1) begin : gen_id_check
        always_comb begin
            for (int i = 0; i < NUM_CORES; i++) begin
                for (int j = 0; j < MAX_OUTSTANDING; j++)
                    outstanding_is_core[i][j] = i == ids[j][2+:$clog2(NUM_CORES)];
            end
    end
    end else begin : gen_no_check
        assign outstanding_is_core = '1;
    end endgenerate

endmodule
