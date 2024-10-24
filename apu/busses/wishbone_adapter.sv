/*
 * Copyright © 2022 Eric Matthews, Chris Keilbart
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module wishbone_adapter

    #(
        parameter int unsigned NUM_CORES = 1
    ) (
        input logic clk,
        input logic rst,

        mem_interface.mem_slave mems[NUM_CORES-1:0],
        wishbone_interface.master wishbone
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
        .write_outstanding('0),
    .*);

    ////////////////////////////////////////////////////
    //Wishbone interface
    //Read bursts and single writes
    logic[4:0] rcount;
    logic[4:0] len;
    logic last;

    always_ff @(posedge clk) begin
        if (rst | request_pop)
            rcount <= '0;
        else
            rcount <= rcount + 5'(wishbone.ack);
    end

    assign request_pop = wishbone.ack & last;
    assign len = {5{request_rnw}} & request_rlen;
    assign last = rcount == len;

    assign wishbone.cyc = request_valid;
    assign wishbone.stb = request_valid;
    assign wishbone.we = ~request_rnw;
    assign wishbone.sel = request_rnw ? '1 : request_wbe;
    assign wishbone.dat_w = request_wdata;
    assign wishbone.bte = 2'b00; //Incrementing burst
    assign wishbone.cti = {last, last, 1'b1}; //End of burst is used even for single-cycle transfers
    assign wishbone.adr[29:5] = request_addr[31:7];
    assign wishbone.adr[4:0] = (request_addr[6:2] & ~len) | (rcount & len);
    

    //Return data registered for frequency
    always_ff @(posedge clk) begin
        request_rdata <= wishbone.dat_r;
        request_rvalid <= request_rnw & wishbone.ack;
        request_rid <= request_id;
    end

endmodule
