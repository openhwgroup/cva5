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

/*
 *  FIFOs Not underflow/overflow safe.
 *  Intended for small FIFO depths.
 *  For continuous operation when full, enqueing side must inspect pop signal
 */
module cva5_fifo

    #(
        parameter type DATA_TYPE = logic,
        parameter FIFO_DEPTH = 4
    )
    (
        input logic clk,
        input logic rst,
        fifo_interface.structure fifo
    );

    localparam LOG2_FIFO_DEPTH = $clog2(FIFO_DEPTH);
    ////////////////////////////////////////////////////
    //Implementation
    //If depth is one, the FIFO can be implemented with a single register
    generate if (FIFO_DEPTH == 1) begin : gen_width_one
        always_ff @ (posedge clk) begin
            if (rst)
                fifo.valid <= 0;
            else if (fifo.push & ~fifo.pop)
                fifo.valid <= 1;
            else if (fifo.pop & ~fifo.push)
                fifo.valid <= 0;
        end
        assign fifo.full = fifo.valid;

        always_ff @ (posedge clk) begin
            if (fifo.potential_push)
                fifo.data_out <= fifo.data_in;
        end
    end
    //If depth is two, the FIFO can be implemented with two registers
    //connected as a shift reg for the same resources as a LUTRAM FIFO
    //but with better timing
    else if (FIFO_DEPTH == 2) begin : gen_width_two
        DATA_TYPE shift_reg [FIFO_DEPTH];
        logic [LOG2_FIFO_DEPTH:0] inflight_count;
        ////////////////////////////////////////////////////
        //Occupancy Tracking
        always_ff @ (posedge clk) begin
            if (rst)
                inflight_count <= 0;
            else
                inflight_count <= inflight_count + (LOG2_FIFO_DEPTH+1)'(fifo.pop) - (LOG2_FIFO_DEPTH+1)'(fifo.push);
        end

        assign fifo.valid = inflight_count[LOG2_FIFO_DEPTH];
        assign fifo.full = fifo.valid & ~|inflight_count[LOG2_FIFO_DEPTH-1:0];

        always_ff @ (posedge clk) begin
            if (fifo.push) begin
                shift_reg[0] <= fifo.data_in;
                shift_reg[1] <= shift_reg[0];
            end
        end

        assign fifo.data_out = shift_reg[~inflight_count[0]];
    end
    else begin : gen_width_3_plus
        logic [LOG2_FIFO_DEPTH-1:0] write_index;
        logic [LOG2_FIFO_DEPTH-1:0] read_index;
        logic [LOG2_FIFO_DEPTH:0] inflight_count;
        ////////////////////////////////////////////////////
        //Occupancy Tracking
        always_ff @ (posedge clk) begin
            if (rst)
                inflight_count <= 0;
            else
                inflight_count <= inflight_count + (LOG2_FIFO_DEPTH+1)'(fifo.pop) - (LOG2_FIFO_DEPTH+1)'(fifo.push);
        end

        assign fifo.valid = inflight_count[LOG2_FIFO_DEPTH];
        assign fifo.full = inflight_count == (LOG2_FIFO_DEPTH+1)'(-FIFO_DEPTH);

        lfsr #(.WIDTH(LOG2_FIFO_DEPTH), .NEEDS_RESET(1))
        lfsr_read_index (
            .clk (clk),.rst (rst),
            .en(fifo.pop),
            .value(read_index)
        );
        lfsr #(.WIDTH(LOG2_FIFO_DEPTH), .NEEDS_RESET(1))
        lfsr_write_index (
            .clk (clk), .rst (rst),
            .en(fifo.push),
            .value(write_index)
        );
        //Force FIFO depth to next power of 2
        lutram_1w_1r #(.DATA_TYPE(DATA_TYPE), .DEPTH(2**LOG2_FIFO_DEPTH))
        write_port (
            .clk(clk),
            .waddr(write_index),
            .raddr(read_index),
            .ram_write(fifo.potential_push),
            .new_ram_data(fifo.data_in),
            .ram_data_out(fifo.data_out)
        );
    end
    endgenerate

    ////////////////////////////////////////////////////
    //Assertions
    fifo_overflow_assertion:
        assert property (@(posedge clk) disable iff (rst) fifo.push |-> (~fifo.full | fifo.pop)) else $error("overflow");
    fifo_potenial_push_overflow_assertion:
        assert property (@(posedge clk) disable iff (rst) fifo.potential_push |-> (~fifo.full | fifo.pop)) else $error("potential push overflow");
    fifo_underflow_assertion:
        assert property (@(posedge clk) disable iff (rst) fifo.pop |-> (fifo.valid | fifo.push)) else $error("underflow");

endmodule
