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

import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module wishbone_master
        (
        input logic clk,
        input logic rst,

        wishbone_interface.master m_wishbone,
        output logic[31:0] data_out,

        input data_access_shared_inputs_t ls_inputs,
        ls_sub_unit_interface.sub_unit ls

        );
    //implementation
    ////////////////////////////////////////////////////

    always_ff @ (posedge clk) begin
        if (ls.new_request) begin
            m_wishbone.addr <= ls_inputs.addr;
            m_wishbone.we <= ls_inputs.store;
            m_wishbone.sel <= ls_inputs.be;
            m_wishbone.writedata <= ls_inputs.data_in;
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
            data_out <= m_wishbone.readdata;
        else
            data_out <= 0;
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
