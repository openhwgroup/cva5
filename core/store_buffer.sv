/*
 * Copyright © 2020 Eric Matthews,  Lesley Shannon
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
import riscv_types::*;
import taiga_types::*;

module store_buffer (
        input logic clk,
        input logic rst,

        store_buffer_request_interface.store_buffer sb_request,
        store_buffer_output_interface.store_buffer sb_output,

        //Load address collision checking
        input logic [31:0] compare_addr,
        input logic compare,
        output logic address_conflict,

        //Writeback data
        input instruction_id_t oldest_id,
        input logic [31:0] writeback_data,
        input logic writeback_valid
        );

    localparam NUM_ENTRIES = MAX_INFLIGHT_COUNT;
    localparam NUM_ENTRIES_W = $clog2(NUM_ENTRIES);

    logic [NUM_ENTRIES-1:0] valid;
    logic [NUM_ENTRIES-1:0] data_valid;

    instruction_id_t required_id_to_store_id_table [NUM_ENTRIES];
    instruction_id_t store_waiting_id;

    localparam TAG_W = 16;
    localparam TAG_OFFSET = 2;

    logic [TAG_W-1:0] tag_addr [NUM_ENTRIES];

    typedef struct packed{
        logic [31:TAG_W] upper_addr;
        logic [1:0] lower_addr;
        logic [2:0] fn3;
    } transaction_attributes_t;

    transaction_attributes_t new_transaction;
    transaction_attributes_t transaction_attributes [NUM_ENTRIES];
    logic [31:0] store_data [NUM_ENTRIES];
    logic [31:0] new_store_data;
    logic [31:0] new_store_data_aligned;
    logic [1:0] data_address_alignment;
    logic writeback_data_match;
    logic update_store_data;

    logic [NUM_ENTRIES-1:0] store_issuing_one_hot;
    logic [NUM_ENTRIES-1:0] new_id_one_hot;
    logic [NUM_ENTRIES-1:0] writeback_store_one_hot;
    ////////////////////////////////////////////////////
    //Implementation
    ////////////////////////////////////////////////////

    //Request attributes that need only a single read-port
    assign new_transaction.upper_addr = sb_request.addr[31:TAG_W];
    assign new_transaction.lower_addr = sb_request.addr[1:0];
    assign new_transaction.fn3 = sb_request.fn3;

    always_ff @ (posedge clk) begin
        if (sb_request.valid)
            transaction_attributes[sb_request.id] <= new_transaction;
    end

    //Address tags in registers for parallel comparisons
    always_ff @ (posedge clk) begin
        foreach(tag_addr[i]) begin
            if (new_id_one_hot[i])
                tag_addr[i] <= sb_request.addr[0+:TAG_W];
        end
    end

    //ID translation table for looking up the store ID from the ID needed by the store
    always_ff @ (posedge clk) begin
        if (sb_request.valid)
            required_id_to_store_id_table[sb_request.data_id] <= sb_request.id;
    end
    assign store_waiting_id = required_id_to_store_id_table[oldest_id];


    assign new_store_data = sb_request.valid ? sb_request.data : writeback_data;
    assign data_address_alignment = sb_request.valid ? sb_request.addr[1:0] : transaction_attributes[store_waiting_id].lower_addr[1:0];
    //Input: ABCD
    //Assuming aligned requests,
    //Possible byte selections: (A/C/D, B/D, C/D, D)
    always_comb begin
        new_store_data_aligned[7:0] = new_store_data[7:0];
        new_store_data_aligned[15:8] = (data_address_alignment[1:0] == 2'b01) ? new_store_data[7:0] : new_store_data[15:8];
        new_store_data_aligned[23:16] = (data_address_alignment[1:0] == 2'b10) ? new_store_data[7:0] : new_store_data[23:16];
        case(data_address_alignment[1:0])
            2'b10 : new_store_data_aligned[31:24] = new_store_data[15:8];
            2'b11 : new_store_data_aligned[31:24] = new_store_data[7:0];
            default : new_store_data_aligned[31:24] = new_store_data[31:24];
        endcase
    end

    //LUTRAM for the store data
    assign writeback_data_match = valid[store_waiting_id] & ~data_valid[store_waiting_id];
    assign update_store_data = (sb_request.valid & sb_request.data_valid) | (writeback_data_match & writeback_valid);
    always_ff @ (posedge clk) begin
        if (update_store_data)
            store_data[sb_request.valid ? sb_request.id : oldest_id] <= new_store_data_aligned;
    end

    always_comb begin
        new_id_one_hot = 0;
        new_id_one_hot[sb_request.id] = sb_request.valid;

        store_issuing_one_hot = 0;
        store_issuing_one_hot[oldest_id] = sb_output.accepted;

        writeback_store_one_hot = 0;
        writeback_store_one_hot[store_waiting_id] = writeback_data_match & writeback_valid;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            valid <= 0;
        else
            valid <= (new_id_one_hot | valid) & ~store_issuing_one_hot;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            data_valid <= 0;
        else
            data_valid <= (({NUM_ENTRIES{sb_request.data_valid}} & new_id_one_hot) | writeback_store_one_hot | data_valid) & ~store_issuing_one_hot;
    end

    assign sb_request.ready = 1;

    ////////////////////////////////////////////////////
    //Collision checking
    always_comb begin
        address_conflict = 0;
        for (int i=0; i < NUM_ENTRIES; i++) begin
            address_conflict |= (tag_addr[i] == compare_addr[0+:TAG_W]) && valid[i];
        end
        address_conflict &= compare;// & |valid;//&= compare;
    end

    ////////////////////////////////////////////////////
    //Output
    assign sb_output.addr = {transaction_attributes[oldest_id].upper_addr, tag_addr[oldest_id]};//jukiiiyuhhhhhhhhhhhhh , transaction_attributes[oldest_id].lower_addr};
    assign sb_output.fn3 = transaction_attributes[oldest_id].fn3;
    assign sb_output.data = store_data[oldest_id];
    assign sb_output.valid = valid[oldest_id] & data_valid[oldest_id];
    assign sb_output.id = oldest_id;

    //Byte enable generation
    //Only set on store
    //  SW: all bytes
    //  SH: upper or lower half of bytes
    //  SB: specific byte
    always_comb begin
        sb_output.be = 0;
        case(sb_output.fn3[1:0])
            LS_B_fn3[1:0] : sb_output.be[sb_output.addr[1:0]] = 1;
            LS_H_fn3[1:0] : begin
                sb_output.be[sb_output.addr[1:0]] = 1;
                sb_output.be[{sb_output.addr[1], 1'b1}] = 1;
            end
            default : sb_output.be = '1;
        endcase
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions


endmodule
