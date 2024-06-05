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

module local_mem_sub_unit

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    (
        input logic clk,
        input logic rst,

        memory_sub_unit_interface.responder unit,
        local_memory_interface.master local_mem
    );

    assign unit.ready = 1;

    assign local_mem.addr = unit.addr[31:2];
    assign local_mem.en = unit.new_request;
    assign local_mem.be = unit.be;
    assign local_mem.data_in = unit.data_in;
    assign unit.data_out = local_mem.data_out;

    always_ff @ (posedge clk) begin
        if (rst)
            unit.data_valid <= 0;
        else
            unit.data_valid <= unit.new_request & unit.re;
    end

endmodule
