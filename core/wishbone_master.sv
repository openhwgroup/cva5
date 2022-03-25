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

module wishbone_master

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    (
        input logic clk,
        input logic rst,

        wishbone_interface.master m_wishbone,
        memory_sub_unit_interface.responder ls
    );
    //implementation
    ////////////////////////////////////////////////////

    always_ff @ (posedge clk) begin
        if (ls.new_request) begin
            m_wishbone.addr <= ls.addr;
            m_wishbone.we <= ls.we;
            m_wishbone.sel <= ls.be;
            m_wishbone.writedata <= ls.data_in;
        end
    end

    set_clr_reg_with_rst #(.SET_OVER_CLR(0), .WIDTH(1), .RST_VALUE(1)) ready_m (
      .clk, .rst,
      .set(m_wishbone.ack),
      .clr(ls.new_request),
      .result(ls.ready)
    );

    always_ff @ (posedge clk) begin
        if (rst)
            ls.data_valid <= 0;
        else if (~m_wishbone.we & m_wishbone.ack)
            ls.data_valid <= 1;
        else
            ls.data_valid <= 0;
    end

    always_ff @ (posedge clk) begin
        if (m_wishbone.ack)
            ls.data_out <= m_wishbone.readdata;
        else
            ls.data_out <= 0;
    end

    always_ff @ (posedge clk) begin
        if (rst) begin
            m_wishbone.stb <= 0;
            m_wishbone.cyc <= 0;
        end
        else if (ls.new_request) begin
            m_wishbone.stb <= 1;
            m_wishbone.cyc <= 1;
        end
        else if (m_wishbone.ack) begin
            m_wishbone.stb <= 0;
            m_wishbone.cyc <= 0;
        end
    end

endmodule
