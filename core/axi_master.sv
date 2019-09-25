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

import taiga_config::*;
import taiga_types::*;


module axi_master
        (
        input logic clk,
        input logic rst,

        axi_interface.master m_axi,
        input logic [2:0] size,
        output logic[31:0] data_out,

        input data_access_shared_inputs_t ls_inputs,
        ls_sub_unit_interface.sub_unit ls

        );
    logic ready;


    //read constants
    assign m_axi.arlen = 0; // 1 request
    assign m_axi.arburst = 0;// burst type does not matter
    assign m_axi.rready = 1; //always ready to receive data

    always_ff @ (posedge clk) begin
        if (ls.new_request) begin
            m_axi.araddr <= ls_inputs.addr;
            m_axi.arsize <= size;
            m_axi.awsize <= size;
            m_axi.awaddr <= ls_inputs.addr;
            m_axi.wdata <= ls_inputs.data_in;
            m_axi.wstrb  <= ls_inputs.be;
        end
    end

    //write constants
    assign m_axi.awlen = 0;
    assign m_axi.awburst = 0;
    assign m_axi.bready = 1;

    always_ff @ (posedge clk) begin
        if (rst)
            ready <= 1;
        else if (ls.new_request)
            ready <= 0;
        else if (m_axi.rvalid | m_axi.bvalid)
            ready <= 1;
    end
    assign ls.ready = ready;

    always_ff @ (posedge clk) begin
        if (rst)
            ls.data_valid <= 0;
        else
            ls.data_valid <= m_axi.rvalid;
    end

    //read channel
    always_ff @ (posedge clk) begin
        if (rst)
            m_axi.arvalid <= 0;
        else if (ls.new_request & ls_inputs.load)
            m_axi.arvalid <= 1;
        else if (m_axi.arready)
            m_axi.arvalid <= 0;
    end

    always_ff @ (posedge clk) begin
        if (m_axi.rvalid)
            data_out <= m_axi.rdata;
    end

    //write channel
    always_ff @ (posedge clk) begin
        if (rst)
            m_axi.awvalid <= 0;
        else if (ls.new_request & ls_inputs.store)
            m_axi.awvalid <= 1;
        else if (m_axi.awready)
            m_axi.awvalid <= 0;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            m_axi.wvalid <= 0;
        else if (ls.new_request & ls_inputs.store)
            m_axi.wvalid <= 1;
        else if (m_axi.wready)
            m_axi.wvalid <= 0;
    end
    assign  m_axi.wlast = m_axi.wvalid;

endmodule
