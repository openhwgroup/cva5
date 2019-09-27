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

module ibram(
        input logic clk,
        input logic rst,

        fetch_sub_unit_interface.sub_unit fetch_sub,
        local_memory_interface.master instruction_bram
        );

    assign fetch_sub.ready = 1;

    assign instruction_bram.addr = fetch_sub.stage1_addr[31:2];
    assign instruction_bram.en = fetch_sub.new_request;
    assign instruction_bram.be = '0;
    assign instruction_bram.data_in = '0;
    assign fetch_sub.data_out =  instruction_bram.data_out;

    always_ff @ (posedge clk) begin
        if (rst | fetch_sub.flush)
            fetch_sub.data_valid <= 0;
        else
            fetch_sub.data_valid <= fetch_sub.new_request;
    end

endmodule
