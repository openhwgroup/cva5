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

        wishbone_interface.master wishbone,
        memory_sub_unit_interface.responder ls
    );

    logic busy;
    ////////////////////////////////////////////////////
    //Implementation
    assign wishbone.cti = 0;
    assign wishbone.bte = 0;

    always_ff @ (posedge clk) begin
        if (ls.new_request) begin
            wishbone.adr <= ls.addr[31:2];
            wishbone.sel <= ls.we ? ls.be : '1;
            wishbone.we <= ls.we;
            wishbone.dat_w <= ls.data_in;
        end
    end

    always_ff @ (posedge clk) begin
        if (rst)
            busy <= 0;
        else
            busy <= (busy & ~wishbone.ack) | ls.new_request;
    end
    assign ls.ready = (~busy);

    assign wishbone.stb = busy;
    assign wishbone.cyc = busy;

    always_ff @ (posedge clk) begin
        if (rst)
            ls.data_valid <= 0;
        else
            ls.data_valid <= ~wishbone.we & wishbone.ack;
    end
    always_ff @ (posedge clk) begin
        if (wishbone.ack)
            ls.data_out <= wishbone.dat_r;
    end

endmodule
