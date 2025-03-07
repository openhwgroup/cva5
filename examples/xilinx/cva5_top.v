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

module cva5_top

    #(
        parameter LOCAL_MEM = "mem.mif",
        parameter WORDS = 1024
    )
    (
        input clk,
        input rstn, //Synchronous active low

        //Peripheral AXI4-Lite bus
        //AR
        input m_axi_arready,
        output m_axi_arvalid,
        output [31:0] m_axi_araddr,

        //R
        output m_axi_rready,
        input m_axi_rvalid,
        input [31:0] m_axi_rdata,
        input [1:0] m_axi_rresp,

        //AW
        input m_axi_awready,
        output m_axi_awvalid,
        output [31:0] m_axi_awaddr,

        //W
        input m_axi_wready,
        output m_axi_wvalid,
        output [31:0] m_axi_wdata,
        output [3:0] m_axi_wstrb,

        //B
        output m_axi_bready,
        input m_axi_bvalid,
        input [1:0] m_axi_bresp
    );

    cva5_wrapper #(.LOCAL_MEM(LOCAL_MEM), .WORDS(WORDS)) cva5_inst(
        .clk(clk),
        .rstn(rstn),
        .m_axi_arready(m_axi_arready),
        .m_axi_arvalid(m_axi_arvalid),
        .m_axi_araddr(m_axi_araddr),
        .m_axi_rready(m_axi_rready),
        .m_axi_rvalid(m_axi_rvalid),
        .m_axi_rdata(m_axi_rdata),
        .m_axi_rresp(m_axi_rresp),
        .m_axi_awready(m_axi_awready),
        .m_axi_awvalid(m_axi_awvalid),
        .m_axi_awaddr(m_axi_awaddr),
        .m_axi_wready(m_axi_wready),
        .m_axi_wvalid(m_axi_wvalid),
        .m_axi_wdata(m_axi_wdata),
        .m_axi_wstrb(m_axi_wstrb),
        .m_axi_bready(m_axi_bready),
        .m_axi_bvalid(m_axi_bvalid),
        .m_axi_bresp(m_axi_bresp)
    );

endmodule
