/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * we_ress required by applicable law or agreed to in writing, software
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
import fpu_types::*;

module dbram(
        input logic clk,
        input logic rst,

        input data_access_shared_inputs_t ls_inputs,
        ls_sub_unit_interface.sub_unit ls,
        output logic[31:0] data_out,

        local_memory_interface.master data_bram
        );

    assign ls.ready = 1;

    assign data_bram.addr = ls_inputs.addr[31:2];
    assign data_bram.en = ls.new_request;
    assign data_bram.be = ls_inputs.be;
    assign data_bram.data_in = ls_inputs.data_in;
    assign data_out = data_bram.data_out;

    always_ff @ (posedge clk) begin
        if (rst)
            ls.data_valid <= 0;
        else
            ls.data_valid <= ls.new_request & ls_inputs.load;
    end

endmodule

module fp_dbram #(parameter INTERFACE_FLEN = 64) (
        input logic clk,
        input logic rst,

        input data_access_shared_inputs_t ls_inputs,
        ls_sub_unit_interface.sub_unit ls,
        output logic[INTERFACE_FLEN-1:0] data_out,

        fp_local_memory_interface.master data_bram
        );

    logic single_read;
    logic we_r;
    logic [INTERFACE_FLEN-1:0] little_endian_data_in;
    assign little_endian_data_in = {ls_inputs.fp_data_in[0+:32], ls_inputs.fp_data_in[INTERFACE_FLEN-1-:32]};
    assign ls.ready = 1;

    assign data_bram.addr = ls_inputs.addr[31:3];
    assign data_bram.en = ls.new_request;
    assign data_bram.be = ls_inputs.be;
    //Treat single writes the same as integer writes
    assign data_bram.we = {ls_inputs.is_float & ~ls_inputs.is_single, ls_inputs.we}; //bit 0 = word select, bit 1 = both
    always_comb begin
        if (ls_inputs.is_float)
            data_bram.data_in = ls_inputs.is_single ? INTERFACE_FLEN'(ls_inputs.fp_data_in[31:0]) : little_endian_data_in;
        else
            data_bram.data_in = INTERFACE_FLEN'(ls_inputs.data_in); //prepend with 32'b0

        if (single_read) begin //TODO: better handling of single/double loads
            data_out[31:0] = '1;
            data_out[63:32] = we_r ? data_bram.data_out[63:32] : data_bram.data_out[31:0];
        end
        else
            data_out = data_bram.data_out;
    end

    always_ff @ (posedge clk) begin
        if (rst) begin
            ls.data_valid <= 0;
            single_read <= 0;
            we_r <= 0;
        end
        else begin
            ls.data_valid <= ls.new_request & ls_inputs.load;
            single_read <= ls.new_request & ls_inputs.load & ls_inputs.is_float & ls_inputs.is_single;
            we_r <= ~ls_inputs.we;
        end

        //if (data_bram.en & |ls_inputs.we)
            //$display("addr:0x%h, write:0x%h", ls_inputs.addr, data_bram.data_in); 
    end

endmodule
