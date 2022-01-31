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
 
module l2_fifo  #(parameter DATA_WIDTH = 32, parameter FIFO_DEPTH = 4, parameter ASYNC = 0)
        (
        input logic clk,
        input logic wr_clk,
        input logic rd_clk,

        input logic rst,
        l2_fifo_interface.structure fifo
        );

    generate if (ASYNC) begin : gen_async

        end
        else
        begin : gen_sync

            if (FIFO_DEPTH == 1) begin
                always_ff @ (posedge clk) begin
                    if (rst)
                        fifo.valid <= 0;
                    else if (fifo.push)
                        fifo.valid <= 1;
                    else
                        fifo.valid <= 0;
                end

                always_ff @ (posedge clk) begin
                    if (fifo.push)
                        fifo.data_out <= fifo.data_in;
                end
            end
            else begin

                logic[DATA_WIDTH-1:0] lut_ram[FIFO_DEPTH-1:0];

                logic[$clog2(FIFO_DEPTH)-1:0] write_index;
                logic[$clog2(FIFO_DEPTH)-1:0] read_index;

                logic count_v [FIFO_DEPTH:0];
                ////////////////////////////////////////////////////////
                //implementation
    
                assign fifo.data_out = lut_ram[read_index];

                always_ff @ (posedge clk) begin
                    if (rst) begin
                        read_index <= '0;
                        write_index <= '0;
                    end            
                    else begin
                        read_index <= read_index + $clog2(FIFO_DEPTH)'(fifo.pop);
                        write_index <= write_index + $clog2(FIFO_DEPTH)'(fifo.push);
                    end
                end

                assign fifo.full = count_v[FIFO_DEPTH];
                assign fifo.valid = ~count_v[0];

                always_ff @ (posedge clk) begin
                    if (fifo.push)
                        lut_ram[write_index] <= fifo.data_in;
                end
    
                always_ff @ (posedge clk) begin
                    if (rst) begin
                        count_v[0] <= 1;
                        for (int i = 1; i <= FIFO_DEPTH; i++) count_v[i] <= 0;
                    end
                    else if (fifo.push & ~fifo.pop) begin
                        count_v[FIFO_DEPTH:1] <= count_v[FIFO_DEPTH-1:0];
                        count_v[0] <= 1'b0;
                    end else if (~fifo.push & fifo.pop) begin
                        count_v[FIFO_DEPTH] <= 1'b0;
                        count_v[FIFO_DEPTH-1:0] <= count_v[FIFO_DEPTH:1];
                    end
                end
            end
        end
    endgenerate

endmodule
