/*
 * Copyright © 2017-2019 Eric Matthews,  Lesley Shannon
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

module write_back(
        input logic clk,
        input logic rst,

        input logic inorder,

        input logic instruction_issued_with_rd,
        input logic store_committed,
        input instruction_id_t store_id,

        unit_writeback_interface.writeback unit_wb[NUM_WB_UNITS-1:0],
        register_file_writeback_interface.writeback rf_wb,
        tracking_interface.wb ti,
        output logic instruction_complete,
        output logic instruction_queue_empty,
        output instruction_id_t oldest_id,

        //Trace signals
        output logic tr_wb_mux_contention
        );
    //////////////////////////////////////

    //Inflight packets
    logic[$bits(inflight_instruction_packet)-1:0] packet_table [MAX_INFLIGHT_COUNT-1:0];

    //aliases for write-back-interface signals
    logic [MAX_INFLIGHT_COUNT-1:0] unit_done_next_cycle [NUM_WB_UNITS-1:0];
    logic [XLEN-1:0] unit_rd [NUM_WB_UNITS-1:0];
    /////

    instruction_id_t issue_id, retired_id, retired_id_r;
    inflight_instruction_packet retired_instruction_packet;

    instruction_id_t id_ordering [MAX_INFLIGHT_COUNT-1:0];
    instruction_id_t id_ordering_post_store [MAX_INFLIGHT_COUNT-1:0];

    logic [MAX_INFLIGHT_COUNT-1:0] id_done;
    logic [MAX_INFLIGHT_COUNT-1:0] id_done_r;

    logic [MAX_INFLIGHT_COUNT-1:0] id_done_ordered;
    logic [MAX_INFLIGHT_COUNT-1:0] id_done_ordered_post_store;

    logic retired, retired_r;
    logic first_cycle_completion_abort;
    ////////////////////////////////////////////////////
    //Implementation

    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    genvar i;
    generate
        for (i=0; i< NUM_WB_UNITS; i++) begin : interface_to_array_g
            assign unit_done_next_cycle[i] = unit_wb[i].done_next_cycle;
            assign unit_rd[i] = unit_wb[i].rd;
            assign unit_wb[i].writeback_instruction_id = retired_id_r;
        end
    endgenerate

    //ID stack.  id_ordering[0] is the next ID to be issued.  Entries filled from
    //MAX_INFLIGHT_COUNT-1 downwards.
    id_stack #(.STACK_DEPTH(MAX_INFLIGHT_COUNT)) instruction_ordering_stack (
            .clk(clk),
            .rst(rst),
            .issued(ti.issued),
            .retired(retired),
            .store_committed(store_committed),
            .store_id(store_id),
            .id_done_ordered(id_done_ordered_post_store),
            .retired_id(retired_id),
            .ordering(id_ordering),
            .ordering_post_store(id_ordering_post_store),
            .id_available(ti.id_available),
            .next_id(issue_id),
            .empty(instruction_queue_empty)
        );

    assign ti.issue_id = issue_id;
    always_comb begin
        ti.issue_id_one_hot = 0;
        ti.issue_id_one_hot[issue_id] = 1;
    end

    //Inflight Instruction ID table
    //Stores unit id (in one-hot encoding), rd_addr and whether rd_addr is zero
    initial begin
        foreach (packet_table[i]) begin
            packet_table[i] = '0;
        end
    end

    always_ff @ (posedge clk) begin
        if (ti.id_available)//instruction_issued_with_rd
            packet_table[issue_id] <= ti.inflight_packet;
    end
    //////////////////////

    //One-hot ID retired last cycle
    logic [MAX_INFLIGHT_COUNT-1:0] id_retired_last_cycle;
    always_comb begin
        id_retired_last_cycle = 0;
        id_retired_last_cycle[retired_id_r] = retired_r;
    end

    //Or together all unit done signals for the same ID.
    always_comb begin
        id_done = (id_done_r & ~id_retired_last_cycle); //Still pending instructions
        for (int i=0; i< NUM_WB_UNITS; i++) begin
            id_done |= unit_done_next_cycle[i];
        end
    end

    always_ff @ (posedge clk) begin
        if (rst)
            id_done_r = '0;
        else
            id_done_r = id_done;
    end

    assign retired = (inorder ? id_done_ordered[MAX_INFLIGHT_COUNT-1] : |id_done);
    always_ff @(posedge clk) begin
        retired_r <= retired;
        retired_id_r <= retired_id;
    end

    assign oldest_id = id_ordering[MAX_INFLIGHT_COUNT-1];

    //Stack ordered from newest to oldest issued instruction
    //Find oldest done.
    always_comb begin
        foreach (id_done[i]) begin
            id_done_ordered[i] = id_done[id_ordering[i]];
            id_done_ordered_post_store[i] = id_done[id_ordering_post_store[i]];
        end

        retired_id = id_ordering[MAX_INFLIGHT_COUNT-1];
        for (int i=MAX_INFLIGHT_COUNT-1; i>0; i--) begin
            if (inorder | id_done_ordered[i])
                break;
            retired_id = id_ordering[i-1];
        end
    end

    //Read table for unit ID (acks, and rd_addr for register file)
    assign retired_instruction_packet = packet_table[retired_id_r];
    assign instruction_complete = retired_r;

    //Register file interaction
    assign rf_wb.rd_addr = retired_instruction_packet.rd_addr;
    assign rf_wb.id = retired_id_r;
    assign rf_wb.valid_write = retired_r;
    assign rf_wb.rd_nzero = retired_instruction_packet.rd_addr_nzero;
    assign rf_wb.rd_data = unit_rd[retired_instruction_packet.unit_id];

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////
    //Trace Interface
    generate if (ENABLE_TRACE_INTERFACE) begin
        //Checks if any two pairs are set indicating mux contention
        always_comb begin
            tr_wb_mux_contention = 0;
            for (int i=0; i<MAX_INFLIGHT_COUNT-1; i++) begin
                    for (int j=i+1; j<MAX_INFLIGHT_COUNT; j++) begin
                        tr_wb_mux_contention |= (id_done[i] & id_done[j]);
                    end
            end
        end
    end
    endgenerate

endmodule
