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
    logic [C_M_AXI_ADDR_WIDTH-1:0] araddr;
    logic [7:0] arlen;
    logic [2:0] arsize;
    logic [1:0] arburst;
    logic [3:0] arcache;
    logic [5:0] arid;

    //read data
    logic rready;
    logic rvalid;
    logic [C_M_AXI_DATA_WIDTH-1:0] rdata;
    logic [1:0] rresp;
    logic rlast;
    logic [5:0] rid;

    //Write channel
    //write address
    logic awready;
    logic awvalid;
    logic [C_M_AXI_ADDR_WIDTH-1:0] awaddr;
    logic [7:0] awlen;
    logic [2:0] awsize;
    logic [1:0] awburst;
    logic [3:0] awcache;
    logic [5:0] awid;

    //write data
    logic wready;
    logic wvalid;
    logic [C_M_AXI_DATA_WIDTH-1:0] wdata;
    logic [(C_M_AXI_DATA_WIDTH/8)-1:0] wstrb;
    logic wlast;

    //write response
    logic bready;
    logic bvalid;
    logic [1:0] bresp;
    logic [5:0] bid;

    modport master (input arready, rvalid, rdata, rresp, rlast, rid, awready, wready, bvalid, bresp, bid,
            output arvalid, araddr, arlen, arsize, arburst, arcache, arid, rready, awvalid, awaddr, awlen, awsize, awburst, awcache, awid,
            wvalid, wdata, wstrb, wlast, bready);

    modport slave (input arvalid, araddr, arlen, arsize, arburst, arcache,
            rready,
            awvalid, awaddr, awlen, awsize, awburst, awcache, arid,
            wvalid, wdata, wstrb, wlast, awid,
            bready,
            output arready, rvalid, rdata, rresp, rlast, rid,
            awready,
            wready,
            bvalid, bresp, bid);

`ifdef __CVA5_FORMAL__
    modport formal (input arready, arvalid, araddr, arlen, arsize, arburst, arcache,
                          rready, rvalid, rdata, rresp, rlast, rid,
                          awready, awvalid, awaddr, awlen, awsize, awburst, awcache, arid,
                          wready, wvalid, wdata, wstrb, wlast, awid,
                          bready, bvalid, bresp, bid);
`endif

endinterface

interface avalon_interface;
    logic [31:0] addr;
    logic read;
    logic write;
    logic [3:0] byteenable;
    logic [31:0] readdata;
    logic [31:0] writedata;
    logic waitrequest;
    logic readdatavalid;
    logic writeresponsevalid;

    modport master (input readdata, waitrequest, readdatavalid, writeresponsevalid,
            output addr, read, write, byteenable, writedata);
    modport slave (output readdata, waitrequest, readdatavalid, writeresponsevalid,
            input addr, read, write, byteenable, writedata);

`ifdef __CVA5_FORMAL__
    modport formal (input readdata, waitrequest, readdatavalid, writeresponsevalid,
                          addr, read, write, byteenable, writedata);
`endif

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

`ifdef __CVA5_FORMAL__
    modport formal (input adr, dat_w, sel, cyc, stb, we, cti, bte, dat_r, ack, err);
`endif

endinterface

interface l1_arbiter_request_interface;
    import l2_config_and_types::*;

    logic [31:0] addr;
    logic [31:0] data ;
    logic rnw ;
    logic [3:0] be;
    logic [4:0] size;
    logic is_amo;
    logic [4:0] amo;

    logic request;
    logic ack;

    modport master (output addr, data, rnw, be, size, is_amo, amo, request, input ack);
    modport slave (input addr, data, rnw, be, size, is_amo, amo, request, output ack);

`ifdef __CVA5_FORMAL__
    modport formal (input addr, data, rnw, be, size, is_amo, amo, request, ack);
`endif

endinterface

interface l1_arbiter_return_interface;
    logic [31:2] inv_addr;
    logic inv_valid;
    logic inv_ack;
    logic [31:0] data;
    logic data_valid;

    modport master (input inv_addr, inv_valid, data, data_valid, output inv_ack);
    modport slave (output inv_addr, inv_valid, data, data_valid, input inv_ack);

`ifdef __CVA5_FORMAL__
    modport formal (input inv_addr, inv_valid, data, data_valid, inv_ack);
`endif

endinterface

