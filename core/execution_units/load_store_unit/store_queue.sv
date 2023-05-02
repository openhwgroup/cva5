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

        store_queue_interface.queue sq,
        input logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] store_forward_wb_group,

        //Address hash (shared by loads and stores)
        input addr_hash_t addr_hash,
        //hash check on adding a load to the queue
        output logic [$clog2(CONFIG.SQ_DEPTH)-1:0] sq_index,
        output logic [$clog2(CONFIG.SQ_DEPTH)-1:0] sq_oldest,
        output logic potential_store_conflict,

        //Writeback snooping
        input wb_packet_t wb_packet [CONFIG.NUM_WB_GROUPS],

        //Retire
        input retire_packet_t store_retire
    );

    localparam LOG2_SQ_DEPTH = $clog2(CONFIG.SQ_DEPTH);
    localparam NUM_OF_FORWARDING_PORTS = CONFIG.NUM_WB_GROUPS - 1;
    typedef logic [LOG2_SQ_DEPTH-1:0] sq_index_t;

    typedef struct packed {
        id_t id_needed;
        logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] wb_group;
        sq_index_t sq_index;
    } retire_table_t;
    retire_table_t retire_table_out;

    wb_packet_t wb_snoop [CONFIG.NUM_WB_GROUPS];

    //Register-based memory blocks
    logic [CONFIG.SQ_DEPTH-1:0] valid;
    logic [CONFIG.SQ_DEPTH-1:0] valid_next;
    addr_hash_t [CONFIG.SQ_DEPTH-1:0] hashes;

    //LUTRAM-based memory blocks
    sq_entry_t output_entry;    
    sq_entry_t output_entry_r;    
    logic [1:0] retire_alignment;

    sq_index_t sq_index_next;
    sq_index_t sq_oldest_next;
    logic [LOG2_SQ_DEPTH:0] released_count;

    logic [CONFIG.SQ_DEPTH-1:0] new_request_one_hot;
    logic [CONFIG.SQ_DEPTH-1:0] issued_one_hot;

    logic [31:0] data_pre_alignment;
    logic [31:0] marshalled_data;
    logic [31:0] sq_data_out;
    ////////////////////////////////////////////////////
    //Implementation     

    //Store Queue indicies
    assign sq_index_next = sq_index + LOG2_SQ_DEPTH'(sq.push);
    assign sq_oldest_next = sq_oldest + LOG2_SQ_DEPTH'(sq.pop);

    always_ff @ (posedge clk) begin
        if (rst) begin 
            sq_index <= 0;
            sq_oldest <= 0;
        end else begin
            sq_index <= sq_index_next;
            sq_oldest <= sq_oldest_next;
        end
    end

    assign new_request_one_hot = CONFIG.SQ_DEPTH'(sq.push) << sq_index;
    assign issued_one_hot = CONFIG.SQ_DEPTH'(sq.pop) << sq_oldest;

    assign valid_next = (valid | new_request_one_hot) & ~issued_one_hot;
    always_ff @ (posedge clk) begin
        if (rst) begin
            valid <= '0;
            sq.full <= 0;
        end else begin
            valid <= valid_next;
            sq.full <= &valid_next;
        end
    end
    assign sq.empty = ~|valid;

    //SQ attributes and issue data
    lutram_1w_1r #(.DATA_TYPE(sq_entry_t), .DEPTH(CONFIG.SQ_DEPTH))
    store_attr (
        .clk(clk),
        .waddr(sq_index),
        .raddr(sq_oldest_next),
        .ram_write(sq.push),
        .new_ram_data('{
            addr : sq.data_in.addr,
            be : sq.data_in.be,
            cache_op : sq.data_in.cache_op,
            data : '0
        }),
        .ram_data_out(output_entry)
    );
    always_ff @ (posedge clk) begin
        output_entry_r <= output_entry;
    end

    lutram_1w_1r #(.DATA_TYPE(logic[1:0]), .DEPTH(MAX_IDS))
    store_alignment (
        .clk(clk),
        .waddr(sq.data_in.id),
        .raddr(store_retire.id),
        .ram_write(sq.push),
        .new_ram_data(sq.data_in.addr[1:0]),
        .ram_data_out(retire_alignment)
    );
    //Compare store addr-hashes against new load addr-hash
    always_comb begin
        potential_store_conflict = 0;
        for (int i = 0; i < CONFIG.SQ_DEPTH; i++)
            potential_store_conflict |= {(valid[i] & ~issued_one_hot[i]), addr_hash} == {1'b1, hashes[i]};
    end
    ////////////////////////////////////////////////////
    //Register-based storage
    //Address hashes
    always_ff @ (posedge clk) begin
        for (int i = 0; i < CONFIG.SQ_DEPTH; i++) begin
            if (new_request_one_hot[i])
                hashes[i] <= addr_hash;
        end
    end
    ////////////////////////////////////////////////////
    //Release Handling
    always_ff @ (posedge clk) begin
        if (rst)
            released_count <= 0;
        else
            released_count <= released_count + (LOG2_SQ_DEPTH + 1)'(store_retire.valid) - (LOG2_SQ_DEPTH + 1)'(sq.pop);
    end

    assign sq.no_released_stores_pending = ~|released_count;

    ////////////////////////////////////////////////////
    //Forwarding and Store Data
    //Forwarding is only needed from multi-cycle writeback ports
    //Currently this is the LS port [1] and the MUL/DIV/CSR port [2]

    always_ff @ (posedge clk) begin
        wb_snoop <= wb_packet;
    end

    lutram_1w_1r #(.DATA_TYPE(retire_table_t), .DEPTH(MAX_IDS))
    store_retire_table_lutram (
        .clk(clk),
        .waddr(sq.data_in.id),
        .raddr(store_retire.id),
        .ram_write(sq.push),
        .new_ram_data('{
            id_needed : sq.data_in.id_needed,
            wb_group : store_forward_wb_group,
            sq_index : sq_index
        }),
        .ram_data_out(retire_table_out)
    );

    logic [31:0] wb_data [NUM_OF_FORWARDING_PORTS+1];

    //Data issued with the store can be stored by store-id
    lutram_1w_1r #(.DATA_TYPE(logic[31:0]), .DEPTH(MAX_IDS))
    non_forwarded_port (
        .clk(clk),
        .waddr(sq.data_in.id),
        .raddr(store_retire.id),
        .ram_write(sq.push),
        .new_ram_data(sq.data_in.data),
        .ram_data_out(wb_data[0])
    );

    //Data from wb ports is stored by ID and then accessed by store-id to store-id-needed translation
    generate
    for (genvar i = 0; i < NUM_OF_FORWARDING_PORTS; i++) begin : lutrams
        lutram_1w_1r #(.DATA_TYPE(logic[31:0]), .DEPTH(MAX_IDS))
        writeback_port (
            .clk(clk),
            .waddr(wb_snoop[i+1].id),
            .raddr(retire_table_out.id_needed),
            .ram_write(wb_snoop[i+1].valid),
            .new_ram_data(wb_snoop[i+1].data),
            .ram_data_out(wb_data[i+1])
        );
    end
    endgenerate

    ////////////////////////////////////////////////////
    //Data Marshalling 
    assign data_pre_alignment = wb_data[retire_table_out.wb_group];
    always_comb begin
        //Input: ABCD
        //Assuming aligned requests,
        //Possible byte selections: (A/C/D, B/D, C/D, D)
        marshalled_data[7:0] = data_pre_alignment[7:0];
        marshalled_data[15:8] = (retire_alignment[1:0] == 2'b01) ? data_pre_alignment[7:0] : data_pre_alignment[15:8];
        marshalled_data[23:16] = (retire_alignment[1:0] == 2'b10) ? data_pre_alignment[7:0] : data_pre_alignment[23:16];
        case(retire_alignment[1:0])
            2'b10 : marshalled_data[31:24] = data_pre_alignment[15:8];
            2'b11 : marshalled_data[31:24] = data_pre_alignment[7:0];
            default : marshalled_data[31:24] = data_pre_alignment[31:24];
        endcase
    end


    //Final storage table for the store queue
    //SQ-index addressed
    lutram_1w_1r #(.DATA_TYPE(logic[31:0]), .DEPTH(CONFIG.SQ_DEPTH))
    sq_data_lutram (
        .clk(clk),
        .waddr(retire_table_out.sq_index),
        .raddr(sq_oldest),
        .ram_write(store_retire.valid),
        .new_ram_data(marshalled_data),
        .ram_data_out(sq_data_out)
    );

    assign sq.valid = |released_count;
    assign sq.data_out = '{
        addr : output_entry_r.addr,
        be : output_entry_r.be,
        cache_op : output_entry_r.cache_op,
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
