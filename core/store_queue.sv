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

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )
    ( 
        input logic clk,
        input logic rst,

        input logic lq_push,
        input logic lq_pop,
        store_queue_interface.queue sq,

        //Address hash (shared by loads and stores)
        input addr_hash_t addr_hash,
        //hash check on adding a load to the queue
        output logic [CONFIG.SQ_DEPTH-1:0] potential_store_conflicts,
        //Load issue collision check
        input logic [CONFIG.SQ_DEPTH-1:0] prev_store_conflicts,
        output logic store_conflict,

        //Writeback snooping
        input wb_packet_t wb_packet [CONFIG.NUM_WB_GROUPS],

        //Retire
        input id_t retire_ids [RETIRE_PORTS],
        input logic retire_port_valid [RETIRE_PORTS]
    );

    localparam LOG2_SQ_DEPTH = $clog2(CONFIG.SQ_DEPTH);
    typedef logic [LOG2_MAX_IDS:0] load_check_count_t;

    wb_packet_t wb_snoop [CONFIG.NUM_WB_GROUPS];
    wb_packet_t wb_snoop_r [CONFIG.NUM_WB_GROUPS];

    //Register-based memory blocks
    logic [CONFIG.SQ_DEPTH-1:0] valid;
    logic [CONFIG.SQ_DEPTH-1:0] valid_next;
    addr_hash_t [CONFIG.SQ_DEPTH-1:0] hashes;
    logic [CONFIG.SQ_DEPTH-1:0] data_needed;
    logic [CONFIG.SQ_DEPTH-1:0] released;
    id_t [CONFIG.SQ_DEPTH-1:0] ids;
    id_t [CONFIG.SQ_DEPTH-1:0] id_needed;
    load_check_count_t [CONFIG.SQ_DEPTH-1:0] load_check_count;
    logic [31:0] store_data [CONFIG.SQ_DEPTH];

    //LUTRAM-based memory blocks
    sq_entry_t sq_entry_in;
    sq_entry_t output_entry;    

    load_check_count_t [CONFIG.SQ_DEPTH-1:0] load_check_count_next;

    logic [LOG2_SQ_DEPTH-1:0] sq_index;
    logic [LOG2_SQ_DEPTH-1:0] sq_index_next;
    logic [LOG2_SQ_DEPTH-1:0] sq_oldest;

    logic [CONFIG.SQ_DEPTH-1:0] new_request_one_hot;
    logic [CONFIG.SQ_DEPTH-1:0] issued_one_hot;

    ////////////////////////////////////////////////////
    //Implementation     
    assign sq_index_next = sq_index +LOG2_SQ_DEPTH'(sq.push);
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
            sq_oldest <= sq_oldest +LOG2_SQ_DEPTH'(sq.pop);
    end

    assign new_request_one_hot = CONFIG.SQ_DEPTH'(sq.push) << sq_index;
    assign issued_one_hot = CONFIG.SQ_DEPTH'(sq.pop) << sq_oldest;

    assign valid_next = (valid | new_request_one_hot) & ~issued_one_hot;
    always_ff @ (posedge clk) begin
        if (rst)
            valid <= '0;
        else
            valid <= valid_next;
    end

    assign sq.empty = ~|valid;

    always_ff @ (posedge clk) begin
        if (rst)
            sq.full <= 0;
        else
            sq.full <= valid_next[sq_index_next] | (|load_check_count_next[sq_index_next]);
    end

    //SQ attributes and issue data
    assign sq_entry_in = '{
        addr : sq.data_in.addr,
        be : sq.data_in.be,
        fn3 : sq.data_in.fn3,
        forwarded_store : sq.data_in.forwarded_store,
        data : sq.data_in.data
    };
    lutram_1w_1r #(.WIDTH($bits(sq_entry_t)), .DEPTH(CONFIG.SQ_DEPTH))
    store_attr (
        .clk(clk),
        .waddr(sq_index),
        .raddr(sq_oldest),
        .ram_write(sq.push),
        .new_ram_data(sq_entry_in),
        .ram_data_out(output_entry)
    );

    //Keep count of the number of pending loads that might need a store result
    //Mask out any store completing on this cycle
    always_comb begin
        for (int i = 0; i < CONFIG.SQ_DEPTH; i++) begin
            potential_store_conflicts[i] = (valid[i] & ~issued_one_hot[i]) & (addr_hash == hashes[i]);
            load_check_count_next[i] = load_check_count[i] 
                + (LOG2_MAX_IDS+1)'({potential_store_conflicts[i] & lq_push}) 
                -  (LOG2_MAX_IDS+1)'({prev_store_conflicts[i] & lq_pop});
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
    //Register-based storage
    //IDs of stores
    //ID needed for forwarded data
    //Address hashes
    always_ff @ (posedge clk) begin
        for (int i = 0; i < CONFIG.SQ_DEPTH; i++) begin
            if (new_request_one_hot[i]) begin
                id_needed[i] <= sq.data_in.id_needed;
                ids[i] <= sq.data_in.id;
                hashes[i] <= addr_hash;
            end
        end
    end

    ////////////////////////////////////////////////////
    //Release Handling
    logic [CONFIG.SQ_DEPTH-1:0] newly_released;
    always_comb begin
        newly_released = '0;
        for (int i = 0; i < CONFIG.SQ_DEPTH; i++)
            for (int j = 0; j < RETIRE_PORTS; j++)
                newly_released[i] |= {1'b1, ids[i]} == {retire_port_valid[j], retire_ids[j]};
    end

    always_ff @ (posedge clk) begin
        if (rst)
            released <= 0;
        else
            released <= (released | (newly_released & valid)) & ~issued_one_hot;
    end

    assign sq.no_released_stores_pending = ~|released;

    ////////////////////////////////////////////////////
    //Forwarding and Store Data
    //Need to support forwarding from any multi-cycle writeback port
    //Currently this is the LS port [1] and the MUL/DIV/CSR port [2]

    always_ff @ (posedge clk) begin
        wb_snoop <= wb_packet;
        wb_snoop_r <= wb_snoop;
    end

    logic [CONFIG.SQ_DEPTH-1:0] write_forward [2];
    always_comb begin
        for (int i = 0; i < CONFIG.SQ_DEPTH; i++) begin
            write_forward[0][i] = CONFIG.INCLUDE_FORWARDING_TO_STORES & {1'b1, wb_snoop_r[1].valid, wb_snoop_r[1].id} == {data_needed[i], 1'b1, id_needed[i]};
            write_forward[1][i] = CONFIG.INCLUDE_FORWARDING_TO_STORES & {1'b1, wb_snoop_r[2].valid, wb_snoop_r[2].id} == {data_needed[i], 1'b1, id_needed[i]};
        end
    end

    always_ff @ (posedge clk) begin
        if (rst)
            data_needed <= 0;
        else
            data_needed <= (data_needed | (new_request_one_hot & {CONFIG.SQ_DEPTH{sq.data_in.forwarded_store}})) & ~(write_forward[0] | write_forward[1]);
    end


    always_ff @ (posedge clk) begin
        for (int i = 0; i < CONFIG.SQ_DEPTH; i++) begin
            if (write_forward[0][i] | write_forward[1][i] | new_request_one_hot[i])
                store_data[i] <= write_forward[0][i] ? wb_snoop_r[1].data : (write_forward[1][i] ? wb_snoop_r[2].data : sq.data_in.data);
        end
    end
    ////////////////////////////////////////////////////
    //Store Transaction Outputs
    logic [31:0] data_pre_alignment;
    logic [31:0] sq_data_out;

    always_comb begin
        //Input: ABCD
        //Assuming aligned requests,
        //Possible byte selections: (A/C/D, B/D, C/D, D)
        data_pre_alignment = store_data[sq_oldest];

        sq_data_out[7:0] = data_pre_alignment[7:0];
        sq_data_out[15:8] = (output_entry.addr[1:0] == 2'b01) ? data_pre_alignment[7:0] : data_pre_alignment[15:8];
        sq_data_out[23:16] = (output_entry.addr[1:0] == 2'b10) ? data_pre_alignment[7:0] : data_pre_alignment[23:16];
        case(output_entry.addr[1:0])
            2'b10 : sq_data_out[31:24] = data_pre_alignment[15:8];
            2'b11 : sq_data_out[31:24] = data_pre_alignment[7:0];
            default : sq_data_out[31:24] = data_pre_alignment[31:24];
        endcase
    end

    assign sq.valid = released[sq_oldest];
    assign sq.data_out = '{
        addr : output_entry.addr,
        be : output_entry.be,
        fn3 : output_entry.fn3,
        forwarded_store : output_entry.forwarded_store,
        data : sq_data_out
    };

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    sq_overflow_assertion:
        assert property (@(posedge clk) disable iff (rst) sq.push |-> (~sq.full | sq.pop)) else $error("sq overflow");
    fifo_underflow_assertion:
        assert property (@(posedge clk) disable iff (rst) sq.pop |-> sq.valid) else $error("sq underflow");


endmodule
