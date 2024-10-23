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
    .*);

    ////////////////////////////////////////////////////
    //AXI interface
    //Read bursts and single writes

    //AR
    assign axi.arvalid = request_valid & request_rnw;
    assign axi.araddr = {request_addr[31:7], request_addr[6:2] & ~request_rlen, 2'b00};
    assign axi.arlen = {3'b0, request_rlen};
    assign axi.arsize = 3'b010; //4 bytes
    assign axi.arburst = 2'b01; //Incrementing
    assign axi.arcache = 4'b0011; //Bufferable and cacheable memory
    assign axi.arlock = 0; //Not locked
    always_comb begin
        axi.arid = '0;
        axi.arid[1+$clog2(NUM_CORES):0] = request_id;
    end

    //R
    assign axi.rready = 1;
    assign request_rdata = axi.rdata;
    assign request_rvalid = axi.rvalid;
    assign request_rid = axi.rid[1+$clog2(NUM_CORES):0];
    //Don't care about rresp or rlast

    //Although it is possible to keep track of the address of outstanding writes,
    //this isn't necessary because reordering is relatively rare on FPGAs

    logic sent_aw;
    logic sent_w;
    always_ff @(posedge clk) begin
        if (rst | axi.bvalid) begin
            sent_aw <= 0;
            sent_w <= 0;
        end
        else begin
            sent_aw <= sent_aw | (axi.awvalid & axi.awready);
            sent_w <= sent_w | (axi.wvalid & axi.wready);
        end
    end

    //AW
    assign axi.awvalid = request_valid & ~request_rnw & ~sent_aw;
    assign axi.awaddr = {request_addr, 2'b00};
    assign axi.awlen = '0;
    assign axi.awsize = 3'b010; //4 bytes
    assign axi.awburst = 2'b01; //Incrementing
    assign axi.awcache = 4'b0011; //Bufferable and cacheable memory
    assign axi.awlock = 0; //Not locked
    always_comb begin
        axi.awid = '0;
        axi.awid[1+$clog2(NUM_CORES):0] = request_id;
    end

    //W
    assign axi.wvalid = request_valid & ~request_rnw & ~sent_w;
    assign axi.wdata = request_wdata;
    assign axi.wstrb = request_wbe;
    assign axi.wlast = 1;

    //B
    assign axi.bready = 1;
    //Don't care about bresp or bid

    assign request_pop = (axi.arvalid & axi.arready) | axi.bvalid;

endmodule
