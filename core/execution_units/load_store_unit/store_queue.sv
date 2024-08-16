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
        input logic [1:0] fp_store_forward_wb_group,

        //Address hash (shared by loads and stores)
        input addr_hash_t addr_hash,

        //hash check on adding a load to the queue
        output logic [$clog2(CONFIG.SQ_DEPTH)-1:0] sq_index,
        output logic [$clog2(CONFIG.SQ_DEPTH)-1:0] sq_oldest,
        output logic potential_store_conflict,

        //Writeback snooping
        input wb_packet_t wb_packet [CONFIG.NUM_WB_GROUPS],
        input fp_wb_packet_t fp_wb_packet [2],

        //Retire
        input retire_packet_t store_retire
    );

    localparam FINAL_TABLE_WIDTH = CONFIG.INCLUDE_UNIT.FPU && FLEN > 32 ? FLEN : 32;
    localparam LOG2_SQ_DEPTH = $clog2(CONFIG.SQ_DEPTH);
    localparam NUM_OF_FORWARDING_PORTS = CONFIG.NUM_WB_GROUPS - 1;
    typedef logic [LOG2_SQ_DEPTH-1:0] sq_index_t;

    typedef struct packed {
        id_t id_needed;
        logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] wb_group;
        logic [1:0] fp_wb_group;
        logic fp;
        sq_index_t sq_index;
    } retire_table_t;
    retire_table_t retire_table_out;

    wb_packet_t wb_snoop [CONFIG.NUM_WB_GROUPS];
    fp_wb_packet_t fp_wb_snoop [2];

    //Register-based memory blocks
    logic [CONFIG.SQ_DEPTH-1:0] valid;
    logic [CONFIG.SQ_DEPTH-1:0] valid_next;
    addr_hash_t [CONFIG.SQ_DEPTH-1:0] hashes;
    logic [CONFIG.SQ_DEPTH-1:0] ids_valid;
    id_t [CONFIG.SQ_DEPTH-1:0] ids;

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
    logic [FLEN-1:0] fp_marshalled_data;
    logic [FINAL_TABLE_WIDTH-1:0] sq_data_in;
    logic [FINAL_TABLE_WIDTH-1:0] sq_data_out;
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
            offset : sq.data_in.offset,
            be : sq.data_in.be,
            cache_op : sq.data_in.cache_op,
            data : '0,
            fp : sq.data_in.fp,
            double : sq.data_in.double,
            fp_data : '0
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
        .new_ram_data(sq.data_in.offset[1:0]),
        .ram_data_out(retire_alignment)
    );
    //Compare store addr-hashes against new load addr-hash
    //ID collisions also handled to prevent overwriting store data
    always_comb begin
        potential_store_conflict = 0;
        for (int i = 0; i < CONFIG.SQ_DEPTH; i++) begin
            potential_store_conflict |= {(valid[i] & ~issued_one_hot[i]), addr_hash} == {1'b1, hashes[i]};
            potential_store_conflict |= {(valid[i] & ~issued_one_hot[i] & ids_valid[i]), sq.data_in.id} == {1'b1, ids[i]};
        end
    end
    ////////////////////////////////////////////////////
    //Register-based storage
    //Address hashes
    always_ff @ (posedge clk) begin
        for (int i = 0; i < CONFIG.SQ_DEPTH; i++) begin
            if (new_request_one_hot[i]) begin
                hashes[i] <= addr_hash;
                ids[i] <= sq.data_in.id_needed;
                ids_valid[i] <= CONFIG.INCLUDE_UNIT.FPU & sq.data_in.fp ? |fp_store_forward_wb_group : |store_forward_wb_group;
            end
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

    ////////////////////////////////////////////////////
    //Forwarding and Store Data
    //Forwarding is only needed from multi-cycle writeback ports
    //Currently this is the LS port [1] and the MUL/DIV/CSR port [2]

    always_ff @ (posedge clk) begin
        wb_snoop <= wb_packet;
        fp_wb_snoop <= fp_wb_packet;
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
            fp_wb_group : fp_store_forward_wb_group,
            fp : sq.data_in.fp,
            sq_index : sq_index
        }),
        .ram_data_out(retire_table_out)
    );

    logic [31:0] wb_data [NUM_OF_FORWARDING_PORTS+1];
    logic [FLEN-1:0] fp_wb_data [3];

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

    generate
    if (CONFIG.INCLUDE_UNIT.FPU) begin : gen_fp_issue_data_storage
        //FP data issued with the store and data from the FP writeback ports is saved
        lutram_1w_1r #(.DATA_TYPE(logic[FLEN-1:0]), .DEPTH(MAX_IDS))
        fp_non_forwarded_port (
            .clk(clk),
            .waddr(sq.data_in.id),
            .raddr(store_retire.id),
            .ram_write(sq.push),
            .new_ram_data(sq.data_in.fp_data),
            .ram_data_out(fp_wb_data[0])
        );
    end
    for (genvar i = 0; i < 2; i++) begin : gen_fp_wb_data_storage
        lutram_1w_1r #(.DATA_TYPE(logic[FLEN-1:0]), .DEPTH(MAX_IDS))
        writeback_port (
            .clk(clk),
            .waddr(fp_wb_snoop[i].id),
            .raddr(retire_table_out.id_needed),
            .ram_write(fp_wb_snoop[i].valid),
            .new_ram_data(fp_wb_snoop[i].data),
            .ram_data_out(fp_wb_data[i+1])
        );
    end
    endgenerate

    ////////////////////////////////////////////////////
    //Data Marshalling 
    assign fp_marshalled_data = fp_wb_data[retire_table_out.fp_wb_group];
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


    //Final storage table for the store queue (includes FP data)
    //SQ-index addressed
    generate
    if (CONFIG.INCLUDE_UNIT.FPU && FLEN > 32) begin : gen_upper_always_fp
        assign sq_data_in[FLEN-1:32] = fp_marshalled_data[FLEN-1:32];
        assign sq_data_in[31:0] = retire_table_out.fp ? fp_marshalled_data[31:0] : marshalled_data[31:0];
    end else if (CONFIG.INCLUDE_UNIT.FPU && FLEN == 32) begin : gen_no_upper
        assign sq_data_in = retire_table_out.fp ? fp_marshalled_data : marshalled_data;
    end else if (CONFIG.INCLUDE_UNIT.FPU && FLEN < 32) begin : gen_upper_always_int
        assign sq_data_in[31:FLEN] = marshalled_data[31:FLEN];
        assign sq_data_in[FLEN-1:0] = retire_table_out.fp ? fp_marshalled_data[FLEN-1:0] : marshalled_data[FLEN-1:0];
    end else begin : gen_no_fpu
        assign sq_data_in = marshalled_data;
    end
    endgenerate

    lutram_1w_1r #(.DATA_TYPE(logic[FINAL_TABLE_WIDTH-1:0]), .DEPTH(CONFIG.SQ_DEPTH))
    sq_data_lutram (
        .clk(clk),
        .waddr(retire_table_out.sq_index),
        .raddr(sq_oldest),
        .ram_write(store_retire.valid),
        .new_ram_data(sq_data_in),
        .ram_data_out(sq_data_out)
    );

    assign sq.valid = |released_count;
    assign sq.data_out = '{
        offset : output_entry_r.offset,
        be : output_entry_r.be,
        cache_op : output_entry_r.cache_op,
        data : sq_data_out[31:0],
        fp : output_entry_r.fp,
        double : output_entry_r.double,
        fp_data : FLEN'(sq_data_out[(CONFIG.INCLUDE_UNIT.FPU ? FLEN : 32)-1:0])
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
