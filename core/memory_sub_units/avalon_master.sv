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

module avalon_master

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    (
        input logic clk,
        input logic rst,

        avalon_interface.master m_avalon,
        memory_sub_unit_interface.responder ls
    );
    //implementation
    ////////////////////////////////////////////////////

    always_ff @ (posedge clk) begin
        if (ls.new_request) begin
            m_avalon.addr <= ls.addr;
            m_avalon.byteenable <= ls.be;
            m_avalon.writedata <= ls.data_in;
        end
    end

    always_ff @ (posedge clk) begin
        if (rst)
            ls.ready <= 1;
        else if (ls.new_request)
            ls.ready <= 0;
        else if (~ls.ready & ~m_avalon.waitrequest)
            ls.ready <= 1;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            ls.data_valid <= 0;
        else if (m_avalon.read & ~m_avalon.waitrequest)
            ls.data_valid <= 1;
        else
            ls.data_valid <= 0;
    end

    always_ff @ (posedge clk) begin
        if (m_avalon.read & ~m_avalon.waitrequest)
            ls.data_out <= m_avalon.readdata;
        else
            ls.data_out <= 0;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            m_avalon.read <= 0;
        else if (ls.new_request & ls.re)
            m_avalon.read <= 1;
        else if (~m_avalon.waitrequest)
            m_avalon.read <= 0;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            m_avalon.write <= 0;
        else if (ls.new_request & ls.we)
            m_avalon.write <= 1;
        else if (~m_avalon.waitrequest)
            m_avalon.write <= 0;
    end



endmodule
