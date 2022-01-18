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

module store_queue

    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;

    # (
        parameter DEPTH = 4
    )
    ( 
        input logic clk,
        input logic rst,

        //Queue status
        output logic sq_empty,
        output logic sq_full,
        output logic no_released_stores_pending,

        //Request interface
        input lsq_entry_t lsq,

        //Address hash (shared by loads and stores)
        input addr_hash_t addr_hash,
        //hash check on adding a load to the queue
        output logic [DEPTH-1:0] potential_store_conflicts,

        //Load issue collision check
        input logic load_issued,
        input logic [DEPTH-1:0] prev_store_conflicts,
        output logic store_conflict,

        //Writeback snooping
        input wb_packet_t wb_snoop,

        //Retire
        input id_t retire_ids [RETIRE_PORTS],
        input logic retire_port_valid [RETIRE_PORTS],

        //lsq output
        output sq_entry_t sq_entry,
        output logic [31:0] sq_data,

        //lsq request handling
        output logic sq_output_valid,
        input logic store_ack
    );

    localparam LOG2_DEPTH = $clog2(DEPTH);
    typedef logic [LOG2_MAX_IDS-1:0] load_check_count_t;


    wb_packet_t wb_snoop_r;

    //Register-based memory blocks
    logic [DEPTH-1:0] valid;
    logic [DEPTH-1:0] valid_next;
    addr_hash_t [DEPTH-1:0] hashes;
    logic [DEPTH-1:0] released;
    id_t [DEPTH-1:0] id_needed;
    id_t [DEPTH-1:0] ids;
    load_check_count_t [DEPTH-1:0] load_check_count;
    (* ramstyle = "MLAB, no_rw_check" *) logic [31:0] store_data_from_issue [DEPTH];
    logic [31:0] store_data_from_wb [DEPTH];

    //LUTRAM-based memory blocks
    (* ramstyle = "MLAB, no_rw_check" *) logic [$bits(sq_entry_t)-1:0] store_attr [DEPTH];

    load_check_count_t [DEPTH-1:0] load_check_count_next;

    logic [LOG2_DEPTH-1:0] sq_index;
    logic [LOG2_DEPTH-1:0] sq_index_next;
    logic [LOG2_DEPTH-1:0] sq_oldest;

    logic [DEPTH-1:0] sq_index_one_hot;
    logic [DEPTH-1:0] sq_oldest_one_hot;

    logic [DEPTH-1:0] new_request_one_hot;
    logic [DEPTH-1:0] issued_one_hot;

    logic new_sq_request;
    logic new_load_request;

    logic [DEPTH-1:0] wb_id_match;

    ////////////////////////////////////////////////////
    //Implementation
    assign new_sq_request = lsq.new_issue & lsq.store;
    assign new_load_request = lsq.new_issue & ~lsq.store;
     
    assign sq_index_next = sq_index + LOG2_DEPTH'(new_sq_request);
    always_ff @ (posedge clk) begin
        if (rst)
            sq_index <= 0;
        else
            sq_index <= sq_index_next;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            sq_oldest <= 0;
        else
            sq_oldest <= sq_oldest + LOG2_DEPTH'(store_ack);
    end
    always_comb begin
        sq_index_one_hot = 0;
        sq_index_one_hot[sq_index] = 1;

        sq_oldest_one_hot = 0;
        sq_oldest_one_hot[sq_oldest] = 1;

        new_request_one_hot = sq_index_one_hot & {DEPTH{new_sq_request}};
        issued_one_hot = sq_oldest_one_hot & {DEPTH{store_ack}};
    end

    assign valid_next = (valid | new_request_one_hot) & ~issued_one_hot;
    always_ff @ (posedge clk) begin
        if (rst)
            valid <= '0;
        else
            valid <= valid_next;
    end

    assign sq_empty = ~|valid;

    always_ff @ (posedge clk) begin
        if (rst)
            sq_full <= 0;
        else
            sq_full <= valid_next[sq_index_next] | (|load_check_count_next[sq_index_next]);
    end
    
    //Attributes LUTRAM
    always_ff @ (posedge clk) begin
        if (new_sq_request)
            store_attr[sq_index] <= {lsq.addr, lsq.be, lsq.fn3, lsq.forwarded_store};
    end

    //Hash mem
    always_ff @ (posedge clk) begin
        if (new_sq_request)
            hashes[sq_index] <= addr_hash;
    end

    //Keep count of the number of pending loads that might need a store result
    //Mask out any store completing on this cycle
    logic [DEPTH-1:0] new_load_waiting;
    logic [DEPTH-1:0] waiting_load_completed;

    always_comb begin
        for (int i = 0; i < DEPTH; i++) begin
            potential_store_conflicts[i] = (valid[i] & ~issued_one_hot[i]) & (addr_hash == hashes[i]);
            new_load_waiting[i] = potential_store_conflicts[i] & new_load_request;
            waiting_load_completed[i] = prev_store_conflicts[i] & load_issued;

            load_check_count_next[i] =
                load_check_count[i]
                + LOG2_MAX_IDS'(new_load_waiting[i])
                - LOG2_MAX_IDS'(waiting_load_completed[i]);
        end
    end
    always_ff @ (posedge clk) begin
        if (rst)
            load_check_count <= '0;
        else
            load_check_count <= load_check_count_next;
    end

    //If a potential blocking store has not been issued yet, the load is blocked until the store(s) complete
    assign store_conflict = |(prev_store_conflicts & valid);


    ////////////////////////////////////////////////////
    //ID Handling

    //ID mem
    always_ff @ (posedge clk) begin
        if (new_sq_request)
            ids[sq_index] <= lsq.id;
    end
    //waiting on ID mem
    always_ff @ (posedge clk) begin
        if (new_sq_request)
            id_needed[sq_index] <= lsq.data_id;
    end

    ////////////////////////////////////////////////////
    //Release Handling
    logic [DEPTH-1:0] newly_released;
    always_comb begin
        for (int i = 0; i < DEPTH; i++) begin
            newly_released[i] = 0;
            for (int j = 0; j < RETIRE_PORTS; j++) begin
                newly_released[i] |= (ids[i] == retire_ids[j]) & retire_port_valid[j];
            end
        end
    end
    always_ff @ (posedge clk) begin
        released <= (released | newly_released) & ~new_request_one_hot;
    end

    assign no_released_stores_pending = ~|(valid & released);

    ////////////////////////////////////////////////////
    //Store Data
    always_ff @ (posedge clk) begin
        wb_snoop_r <= wb_snoop;
    end

    always_ff @ (posedge clk) begin
        for (int i = 0; i < DEPTH; i++) begin
            if ({1'b0, wb_snoop_r.valid, wb_snoop_r.id} == {released[i], 1'b1, id_needed[i]})
                store_data_from_wb[i] <= wb_snoop_r.data;
        end
    end
    
    always_ff @ (posedge clk) begin
        if (new_sq_request & ~lsq.forwarded_store)
            store_data_from_issue[sq_index] <= lsq.data_in;
    end

    ////////////////////////////////////////////////////
    //Store Transaction Outputs
    logic [31:0] data_for_alignment;
    sq_entry_t output_attr;

    assign sq_output_valid = valid[sq_oldest] & released[sq_oldest];
    
    assign output_attr = store_attr[sq_oldest];

    assign sq_entry.addr = output_attr.addr;
    assign sq_entry.be = output_attr.be;
    assign sq_entry.fn3 = output_attr.fn3;

    always_comb begin
        //Input: ABCD
        //Assuming aligned requests,
        //Possible byte selections: (A/C/D, B/D, C/D, D)
        data_for_alignment = output_attr.forwarded_store ? store_data_from_wb[sq_oldest] : store_data_from_issue[sq_oldest];

        sq_data[7:0] = data_for_alignment[7:0];
        sq_data[15:8] = (sq_entry.addr[1:0] == 2'b01) ? data_for_alignment[7:0] : data_for_alignment[15:8];
        sq_data[23:16] = (sq_entry.addr[1:0] == 2'b10) ? data_for_alignment[7:0] : data_for_alignment[23:16];
        case(sq_entry.addr[1:0])
            2'b10 : sq_data[31:24] = data_for_alignment[15:8];
            2'b11 : sq_data[31:24] = data_for_alignment[7:0];
            default : sq_data[31:24] = data_for_alignment[31:24];
        endcase
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
