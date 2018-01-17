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

/*
 *  FIFOs Not underflow/overflow safe.
 *  Intended for small FIFO depths.
 */
module taiga_fifo #(parameter DATA_WIDTH = 42, parameter FIFO_DEPTH = 4, parameter fifo_type_t FIFO_TYPE = NON_MUXED_INPUT_FIFO)
        (
        input logic clk,
        input logic rst,
        fifo_interface.structure fifo
        );

    logic[DATA_WIDTH-1:0] lut_ram[FIFO_DEPTH-1:0];
    logic[DATA_WIDTH-1:0] shift_reg[FIFO_DEPTH-1:0];
    logic[DATA_WIDTH-1:0] shift_reg_new[FIFO_DEPTH-1:0];

    logic[$clog2(FIFO_DEPTH)-1:0] write_index;
    logic[$clog2(FIFO_DEPTH)-1:0] read_index;

    logic two_plus;
    logic[FIFO_DEPTH:0] valid_chain;
    genvar i;

    //implementation
    ////////////////////////////////////////////////////
    //Occupancy Tracking
    always_ff @ (posedge clk) begin
        if (rst)
            valid_chain <= 1;
        else if (fifo.push & ~fifo.pop)
            valid_chain <= {valid_chain[FIFO_DEPTH-1:0], 1'b0};
        else if (fifo.pop & ~fifo.push)
            valid_chain <= {1'b0, valid_chain[FIFO_DEPTH:1]};
    end

    assign fifo.empty = valid_chain[0];
    assign fifo.valid = ~valid_chain[0];
    assign fifo.full = valid_chain[FIFO_DEPTH];
    assign fifo.early_full = valid_chain[FIFO_DEPTH-1] | valid_chain[FIFO_DEPTH];

    //pushing, or more than one, or at least one and not popping
    assign two_plus = ~valid_chain[0] & ~valid_chain[1];
    assign fifo.early_valid = fifo.push | (two_plus) | (fifo.valid & ~fifo.pop);

    ////////////////////////////////////////////////////
    //LUT-RAM version
    generate if (FIFO_TYPE == LUTRAM_FIFO) begin
    ////////////////////////////////////////////////////

            always_ff @ (posedge clk) begin
                if (rst) begin
                    read_index <= '0;
                    write_index <= '0;
                end
                else begin
                    read_index <= read_index + fifo.pop;
                    write_index <= write_index + fifo.push;
                end
            end

            assign fifo.data_out = lut_ram[read_index];

            always_ff @ (posedge clk) begin
                if (fifo.push)
                    lut_ram[write_index] <= fifo.data_in;
            end

        end
    endgenerate
    ////////////////////////////////////////////////////
    //SRL version
    generate if (FIFO_TYPE == NON_MUXED_INPUT_FIFO) begin
    ////////////////////////////////////////////////////

            always_ff @ (posedge clk) begin
                if (rst)
                    read_index <= 0;
                else if ((fifo.valid & fifo.push) | (two_plus & fifo.pop))
                    read_index <= read_index + fifo.push - fifo.pop;
            end

            assign fifo.data_out = shift_reg[read_index];

            always_ff @ (posedge clk) begin
                if (fifo.push)
                    shift_reg[0] <= fifo.data_in;
            end

            for (i=1 ; i < FIFO_DEPTH; i++) begin : shift_reg_gen
                always_ff @ (posedge clk) begin
                    if (fifo.push)
                        shift_reg[i] <= shift_reg[i-1];
                end
            end

        end
    endgenerate
    ////////////////////////////////////////////////////
    //Non-muxed output version
    generate if (FIFO_TYPE == NON_MUXED_OUTPUT_FIFO) begin
    ////////////////////////////////////////////////////

            always_ff @ (posedge clk) begin
                if (rst)
                    write_index <= 0;
                else
                    write_index <= write_index + fifo.push - fifo.pop;
            end

            assign fifo.data_out = shift_reg[0];

            for (i=0 ; i <FIFO_DEPTH; i++) begin : new_reg_non_muxed_gen
                always_comb begin
                    if (fifo.push && write_index == i)
                        shift_reg_new[i] =  fifo.data_in;
                    else
                        shift_reg_new[i] = shift_reg[i];
                end
            end

            always_ff @ (posedge clk) begin
                shift_reg[FIFO_DEPTH-1] <= shift_reg_new[FIFO_DEPTH-1];
            end

            for (i=0 ; i < FIFO_DEPTH-1; i++) begin : shift_reg_non_muxed_gen
                always_ff @ (posedge clk) begin
                    if (fifo.pop)
                        shift_reg[i] <= shift_reg_new[i+1];
                    else
                        shift_reg[i] <= shift_reg_new[i];
                end
            end

        end
    endgenerate
    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert (!(~rst & valid_chain[FIFO_DEPTH] & fifo.push)) else $error("fifo overflow");
        assert (!(~rst & valid_chain[0] & fifo.pop)) else $error("fifo underflow");
    end

endmodule


