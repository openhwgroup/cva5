/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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

module axi_master

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    (
        input logic clk,
        input logic rst,

        axi_interface.master m_axi,
        input logic [2:0] size,
        memory_sub_unit_interface.responder ls

    );
    logic ready;


    //read constants
    assign m_axi.arlen = 0; // 1 request
    assign m_axi.arburst = 0;// burst type does not matter
    assign m_axi.rready = 1; //always ready to receive data

    always_ff @ (posedge clk) begin
        if (ls.new_request) begin
            m_axi.araddr <= ls.addr;
            m_axi.arsize <= size;
            m_axi.awsize <= size;
            m_axi.awaddr <= ls.addr;
            m_axi.wdata <= ls.data_in;
            m_axi.wstrb  <= ls.be;
        end
    end

    //write constants
    assign m_axi.awlen = 0;
    assign m_axi.awburst = 0;
    assign m_axi.bready = 1;

    set_clr_reg_with_rst #(.SET_OVER_CLR(0), .WIDTH(1), .RST_VALUE(1)) ready_m (
      .clk, .rst,
      .set(m_axi.rvalid | m_axi.bvalid),
      .clr(ls.new_request),
      .result(ready)
    );
    assign ls.ready = ready;

    always_ff @ (posedge clk) begin
        if (rst)
            ls.data_valid <= 0;
        else
            ls.data_valid <= m_axi.rvalid;
    end

    //read channel
    set_clr_reg_with_rst #(.SET_OVER_CLR(1), .WIDTH(1), .RST_VALUE(0)) arvalid_m (
      .clk, .rst,
      .set(ls.new_request & ls.re),
      .clr(m_axi.arready),
      .result(m_axi.arvalid)
    );

    always_ff @ (posedge clk) begin
        if (m_axi.rvalid)
            ls.data_out <= m_axi.rdata;
    end

    //write channel
    set_clr_reg_with_rst #(.SET_OVER_CLR(1), .WIDTH(1), .RST_VALUE(0)) awvalid_m (
      .clk, .rst,
      .set(ls.new_request & ls.we),
      .clr(m_axi.awready),
      .result(m_axi.awvalid)
    );

    set_clr_reg_with_rst #(.SET_OVER_CLR(1), .WIDTH(1), .RST_VALUE(0)) wvalid_m (
      .clk, .rst,
      .set(ls.new_request & ls.we),
      .clr(m_axi.wready),
      .result(m_axi.wvalid)
    );
    assign  m_axi.wlast = m_axi.wvalid;

endmodule
