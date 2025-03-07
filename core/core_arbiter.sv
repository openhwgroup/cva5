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

module core_arbiter

    #(
        parameter logic INCLUDE_DCACHE = 1'b1,
        parameter logic INCLUDE_ICACHE = 1'b1,
        parameter logic INCLUDE_MMUS = 1'b1
    ) (
        input logic clk,
        input logic rst,

        mem_interface.rw_slave dcache,
        mem_interface.ro_slave icache,
        mem_interface.ro_slave dmmu,
        mem_interface.ro_slave immu,
        mem_interface.mem_master mem
    );

    //Multiplexes memory requests and demultiplexes memory responses
    //If the MMUs are not present the MSB of the memory ID is always 0
    //If the I$ is also not present the entire ID can be set to 0

    logic[3:0] request;
    logic[3:0][31:2] addr;
    logic[3:0][4:0] rlen;
    logic[3:0] rnw;
    logic[3:0] rmw;
    logic[1:0] port;

    ////////////////////////////////////////////////////
    //Implementation

    //D$
    assign request[0] = INCLUDE_DCACHE ? dcache.request : 0;
    assign addr[0] = INCLUDE_DCACHE ? dcache.addr : 'x;
    assign rlen[0] = INCLUDE_DCACHE ? dcache.rlen : 'x;
    assign rnw[0] = INCLUDE_DCACHE ? dcache.rnw : 'x;
    assign rmw[0] = INCLUDE_DCACHE ? dcache.rmw : 'x;
    assign mem.wbe = dcache.wbe;
    assign mem.wdata = dcache.wdata;
    assign dcache.inv = mem.inv;
    assign dcache.inv_addr = mem.inv_addr;
    assign dcache.write_outstanding = mem.write_outstanding;
    assign dcache.ack = mem.ack & port == 2'b00;
    assign dcache.rvalid = mem.rvalid & mem.rid == 2'b00;
    assign dcache.rdata = mem.rdata;
    //I$
    assign request[1] = INCLUDE_ICACHE ? icache.request : 0;
    assign addr[1] = INCLUDE_ICACHE ? icache.addr : 'x;
    assign rlen[1] = INCLUDE_ICACHE ? icache.rlen : 'x;
    assign rnw[1] = INCLUDE_ICACHE ? 1 : 'x;
    assign rmw[1] = INCLUDE_ICACHE ? 0 : 'x;
    assign icache.ack = mem.ack & port == 2'b01;
    assign icache.rvalid = mem.rvalid & mem.rid == 2'b01;
    assign icache.rdata = mem.rdata;
    //DMMU
    assign request[2] = INCLUDE_MMUS ? dmmu.request : 0;
    assign addr[2] = INCLUDE_MMUS ? dmmu.addr : 'x;
    assign rlen[2] = INCLUDE_MMUS ? dmmu.rlen : 'x;
    assign rnw[2] = INCLUDE_MMUS ? 1 : 'x;
    assign rmw[2] = INCLUDE_MMUS ? 0 : 'x;
    assign dmmu.rdata = mem.rdata;
    assign dmmu.ack = mem.ack & port == 2'b10;
    assign dmmu.rvalid = mem.rvalid & mem.rid == 2'b10;
    //IMMU
    assign request[3] = INCLUDE_MMUS ? immu.request : 0;
    assign addr[3] = INCLUDE_MMUS ? immu.addr : 'x;
    assign rlen[3] = INCLUDE_MMUS ? immu.rlen : 'x;
    assign rnw[3] = INCLUDE_MMUS ? 1 : 'x;
    assign rmw[3] = INCLUDE_MMUS ? 0 : 'x;
    assign immu.rdata = mem.rdata;
    assign immu.ack = mem.ack & port == 2'b11;
    assign immu.rvalid = mem.rvalid & mem.rid == 2'b11;

    
    ////////////////////////////////////////////////////
    //Arbitration
    round_robin #(.NUM_PORTS(4)) rr (
        .requests(request),
        .grant(mem.request & mem.ack),
        .grantee(port),
    .*);

    assign mem.request = |request;
    assign mem.addr = addr[port];
    assign mem.rlen = rlen[port];
    assign mem.rnw = rnw[port];
    assign mem.rmw = rmw[port];
    assign mem.id = port;

endmodule
