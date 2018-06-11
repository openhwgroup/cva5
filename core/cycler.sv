/*
 * Copyright © 2017, 2018 Eric Matthews,  Lesley Shannon
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


module  cycler
        #(
        parameter C_WIDTH = 2
        )
        (
        input logic clk,
        input logic rst,
        input logic en,
        output logic [C_WIDTH - 1: 0] one_hot
        );

    generate
        if (C_WIDTH == 1) begin
            assign one_hot = 1;
        end
        else begin
            always_ff @ (posedge clk) begin
                if (rst)
                    one_hot <= 1;
                else if (en)
                    one_hot <= {one_hot[C_WIDTH-2:0],one_hot[C_WIDTH-1]};//rotate left
            end
        end
    endgenerate

endmodule
