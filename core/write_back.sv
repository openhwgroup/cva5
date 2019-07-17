/*
 * Copyright © 2017, 2018, 2019 Eric Matthews,  Lesley Shannon
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
        input logic gc_supress_writeback,

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
    inflight_instruction_packet packet_table [MAX_INFLIGHT_COUNT-1:0];

    //aliases for write-back-interface signals
    logic [NUM_WB_UNITS-1:0] unit_done_next_cycle;
    instruction_id_t unit_instruction_id [NUM_WB_UNITS-1:0];
    logic [XLEN-1:0] unit_rd [NUM_WB_UNITS-1:0];
    logic [NUM_WB_UNITS-1:0] accepted;
    /////

    instruction_id_t issue_id, retired_id, retired_id_r;
    inflight_instruction_packet retired_instruction_packet;

    instruction_id_t id_ordering [MAX_INFLIGHT_COUNT-1:0];
    instruction_id_t id_ordering_post_store [MAX_INFLIGHT_COUNT-1:0];

    logic [MAX_INFLIGHT_COUNT-1:0] id_done;
    logic [MAX_INFLIGHT_COUNT-1:0] id_done_next;
    logic [MAX_INFLIGHT_COUNT-1:0] id_done_r;

    logic [MAX_INFLIGHT_COUNT-1:0] shift_bits;
    logic [MAX_INFLIGHT_COUNT-1:0] store_shift_bits;

    logic retired, retired_r;
    logic first_cycle_completion_abort;
    //////////////////////////////////////////

    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    genvar i;
    generate
        for (i=0; i< NUM_WB_UNITS; i++) begin : interface_to_array_g
            assign unit_done_next_cycle[i] = unit_wb[i].done_next_cycle;
            assign unit_instruction_id[i] = unit_wb[i].instruction_id;
            assign unit_rd[i] = unit_wb[i].rd;
            assign unit_wb[i].accepted = accepted[i];
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
            .shift_bits(shift_bits),
            .store_shift_bits(store_shift_bits),
            .retired_id(retired_id),
            .ordering(id_ordering),
            .ordering_post_store(id_ordering_post_store),
            .id_available(ti.id_available),
            .next_id(issue_id),
            .empty(instruction_queue_empty)
        );

    assign ti.issue_id = issue_id;

    //Inflight Instruction ID table
    //Stores unit id (in one-hot encoding), rd_addr and whether rd_addr is zero
    initial begin
        foreach (packet_table[i]) begin
            packet_table[i] = '0;
        end
    end

    always_ff @ (posedge clk) begin
        if (instruction_issued_with_rd)
            packet_table[issue_id] <= ti.inflight_packet;
    end
    //////////////////////


    //Or together all unit done signals for the same ID.
    //Inclusion of ti.issue results in id_done_r being the longest path.
    //TODO: possible fix, remove ti.issue from here.  Consequence: on next cycle,
    //a single cycle unit (ALU/BRANCH) will be marked falsely as done, however,
    //the oldest instruction will still have been selected (if any are done).  As such,
    //this can be mitigated by clearing the done_r on the next cycle / masking for
    //the next cycle comparison purposes.
    always_comb begin
        id_done_next = 0;
        for (int i=0; i<MAX_INFLIGHT_COUNT; i++) begin
            for (int j=0; j<NUM_WB_UNITS; j++) begin
                id_done_next[i] |= (unit_instruction_id[j] == i && unit_done_next_cycle[j])  && ~(ti.id_available && issue_id == i && ~ti.issued);
            end
        end
    end

    //If not servicing a unit on the next cycle, save its done status
    always_ff @ (posedge clk) begin
        for (int i=0; i<MAX_INFLIGHT_COUNT; i++) begin
            if (rst || (retired && retired_id == i))
                id_done_r[i] = 0;
            else if (id_done_next[i])
                id_done_r[i] = 1;
        end
    end

    //ID done is a combination of newly completed and already completed instructions
    always_comb begin
        for (int i=0; i<MAX_INFLIGHT_COUNT; i++) begin
            id_done[i] = id_done_r[i] | id_done_next[i];
        end
    end

    assign oldest_id = id_ordering[MAX_INFLIGHT_COUNT-1];

    assign retired = (inorder ? id_done_ordered[MAX_INFLIGHT_COUNT-1] : |id_done);
    always_ff @(posedge clk) begin
        retired_r <= retired;
        retired_id_r <= retired_id;
    end

    //Stack ordered from newest to oldest issued instruction
    //Find oldest done.
    logic [MAX_INFLIGHT_COUNT-1:0] id_done_ordered;
    always_comb begin
        foreach (id_done[i]) begin
            id_done_ordered[i] = id_done[id_ordering_post_store[i]];
        end

        //Lowest entry always shifted, each older entry shifts all below
        store_shift_bits = 0;
        store_shift_bits[0] = 1;
        for (int i=1; i<MAX_INFLIGHT_COUNT; i++) begin
            if (store_committed && id_ordering[i] == store_id)
                store_shift_bits |= (2**(i+1)-1);
        end

        shift_bits = 0;
        shift_bits[0] = 1;
        for (int i=1; i<MAX_INFLIGHT_COUNT; i++) begin
            if (id_done_ordered[i])
                shift_bits |= (2**(i+1)-1);
        end

        retired_id = id_ordering_post_store[0];
        for (int i=1; i<MAX_INFLIGHT_COUNT; i++) begin
            if (id_done_ordered[i]) begin
                retired_id = id_ordering_post_store[i];
            end
        end

        if (inorder)
            retired_id = id_ordering_post_store[MAX_INFLIGHT_COUNT-1];

        if (~|id_done_ordered[MAX_INFLIGHT_COUNT-1:1])
            retired_id = issue_id;

    end

    //Read table for unit ID (acks, and rd_addr for register file)
    assign retired_instruction_packet = packet_table[retired_id_r];
    assign accepted = retired_instruction_packet.unit_id & {NUM_WB_UNITS{retired_r}};

    assign instruction_complete = retired_r;

    //Register file interaction
    assign rf_wb.rd_addr = retired_instruction_packet.rd_addr;
    assign rf_wb.id = retired_id_r;
    assign rf_wb.valid_write = retired_r & retired_instruction_packet.rd_addr_nzero & ~gc_supress_writeback;

    always_comb begin
        rf_wb.rd_data = 0;
        for (int i=0; i< NUM_WB_UNITS; i++) begin
            rf_wb.rd_data |= unit_rd[i] & {32{retired_instruction_packet.unit_id[i]}};
        end
    end

    assign rf_wb.rs1_data_out = ({32{rf_wb.forward_rs1}}  & rf_wb.rd_data) | rf_wb.rs1_data_in;
    assign rf_wb.rs2_data_out = ({32{rf_wb.forward_rs2}}  & rf_wb.rd_data) | rf_wb.rs2_data_in;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////
    //Trace Interface

    //Checks if any two pairs are set indicating mux contention
    always_comb begin
        tr_wb_mux_contention = 0;
        for (int i=0; i<NUM_WB_UNITS; i++) begin
                for (int j=i+1; j<NUM_WB_UNITS; j++) begin
                    tr_wb_mux_contention |= (id_done[i] & id_done[j]);
                end
        end
    end

endmodule
