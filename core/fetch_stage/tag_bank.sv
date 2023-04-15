/*
 * Copyright © 2017-2020 Eric Matthews,  Lesley Shannon
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

module tag_bank  
    #(
        parameter WIDTH = 32,
        parameter LINES = 512
    )
    (
        input logic clk,
        input logic rst,

        input logic[$clog2(LINES)-1:0] addr_a,
        input logic[$clog2(LINES)-1:0] addr_b,
        input logic en_a,
        input logic en_b,
        input logic wen_a,
        input logic wen_b,
        input logic [WIDTH-1:0] data_in_a,
        input logic [WIDTH-1:0] data_in_b,
        output logic [WIDTH-1:0] data_out_a,
        output logic [WIDTH-1:0] data_out_b
    );

    (* ram_style = "block", ramstyle = "no_rw_check" *) logic  [WIDTH-1:0] tag_entry [LINES];
    initial tag_entry = '{default: 0};

    always_ff @ (posedge clk) begin
        if (en_a) begin
            if (wen_a)
                tag_entry[addr_a] <= data_in_a;
            else
                data_out_a <= tag_entry[addr_a];
        end
    end

    always_ff @ (posedge clk) begin
        if (en_b) begin
            if (wen_b)
                tag_entry[addr_b] <= data_in_b;
            else
                data_out_b <= tag_entry[addr_b];
        end
    end

endmodule