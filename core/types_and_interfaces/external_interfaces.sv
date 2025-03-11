/*
 * Copyright © 2019 Eric Matthews,  Lesley Shannon
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

interface axi_interface;
    import cva5_config::*;

    logic arready;
    logic arvalid;
    logic [31:0] araddr;
    logic [7:0] arlen;
    logic [2:0] arsize;
    logic [1:0] arburst;
    logic [3:0] arcache;
    logic [5:0] arid;
    logic arlock;

    //read data
    logic rready;
    logic rvalid;
    logic [31:0] rdata;
    logic [1:0] rresp;
    logic rlast;
    logic [5:0] rid;

    //Write channel
    //write address
    logic awready;
    logic awvalid;
    logic [31:0] awaddr;
    logic [7:0] awlen;
    logic [2:0] awsize;
    logic [1:0] awburst;
    logic [3:0] awcache;
    logic [5:0] awid;
    logic awlock;

    //write data
    logic wready;
    logic wvalid;
    logic [31:0] wdata;
    logic [3:0] wstrb;
    logic wlast;

    //write response
    logic bready;
    logic bvalid;
    logic [1:0] bresp;
    logic [5:0] bid;

    modport master (input arready, rvalid, rdata, rresp, rlast, rid, awready, wready, bvalid, bresp, bid,
            output arvalid, araddr, arlen, arsize, arburst, arcache, arlock, arid, rready, awvalid, awaddr, awlen, awsize, awburst, awcache, awid, awlock,
            wvalid, wdata, wstrb, wlast, bready);

    modport slave (input arvalid, araddr, arlen, arsize, arburst, arcache, arlock,
            rready,
            awvalid, awaddr, awlen, awsize, awburst, awcache, awlock, arid,
            wvalid, wdata, wstrb, wlast, awid,
            bready,
            output arready, rvalid, rdata, rresp, rlast, rid,
            awready,
            wready,
            bvalid, bresp, bid);

endinterface

interface avalon_interface;
    logic [31:0] addr;
    logic read;
    logic write;
    logic lock;
    logic [3:0] byteenable;
    logic [31:0] readdata;
    logic [31:0] writedata;
    logic waitrequest;
    logic readdatavalid;
    logic writeresponsevalid;

    modport master (input readdata, waitrequest, readdatavalid, writeresponsevalid,
            output addr, read, write, lock, byteenable, writedata);
    modport slave (output readdata, waitrequest, readdatavalid, writeresponsevalid,
            input addr, read, write, lock, byteenable, writedata);

endinterface

interface wishbone_interface;
    logic [29:0] adr;
    logic [31:0] dat_w;
    logic [3:0] sel;
    logic cyc;
    logic stb;
    logic we;
    logic [2:0] cti;
    logic [1:0] bte;
    logic [31:0] dat_r;
    logic ack;
    logic err;

    modport master (input dat_r, ack, err,
            output adr, dat_w, sel, cyc, stb, we, cti, bte);
    modport slave (output dat_r, ack, err,
            input adr, dat_w, sel, cyc, stb, we, cti, bte);

endinterface

interface mem_interface;
    logic request;
    logic[31:2] addr;
    logic[4:0] rlen; //Nobody truly needs requests > 32 words
    logic ack;

    logic rvalid;
    logic[31:0] rdata;
    logic[1:0] rid;
    
    logic rnw;
    logic rmw;
    logic[3:0] wbe;
    logic[31:0] wdata;

    logic inv;
    logic[31:2] inv_addr;
    logic write_outstanding;

    logic[1:0] id;

    modport ro_master (output request, addr, rlen, input ack, rvalid, rdata);
    modport ro_slave (input request, addr, rlen, output ack, rvalid, rdata);
    modport rw_master (output request, addr, rlen, rnw, rmw, wbe, wdata, input ack, rvalid, rdata, inv, inv_addr, write_outstanding);
    modport rw_slave (input request, addr, rlen, rnw, rmw, wbe, wdata, output ack, rvalid, rdata, inv, inv_addr, write_outstanding);
    modport mem_master (output request, addr, rlen, rnw, rmw, wbe, wdata, id, input ack, rvalid, rdata, rid, inv, inv_addr, write_outstanding);
    modport mem_slave (input request, addr, rlen, rnw, rmw, wbe, wdata, id, output ack, rvalid, rdata, rid, inv, inv_addr, write_outstanding);

endinterface

interface local_memory_interface;
    logic[29:0] addr;
    logic en;
    logic[3:0] be;
    logic[31:0] data_in;
    logic[31:0] data_out;

    modport slave (input addr, en, be, data_in, output data_out);
    modport master (output addr, en, be, data_in, input data_out);

endinterface
