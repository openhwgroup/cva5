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

module load_store_queue //ID-based input buffer for Load/Store Unit

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    import fpu_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )
    (
        input logic clk,
        input logic rst,
        input gc_outputs_t gc,

        load_store_queue_interface.queue lsq,
        input logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] store_forward_wb_group,
        input logic [1:0] fp_store_forward_wb_group,
        //Writeback snooping
        input wb_packet_t wb_packet [CONFIG.NUM_WB_GROUPS],
        input fp_wb_packet_t fp_wb_packet [2],

        //Retire release
        input retire_packet_t store_retire
    );
    localparam LOG2_SQ_DEPTH = $clog2(CONFIG.SQ_DEPTH);
    localparam DOUBLE_MIN_WIDTH = FLEN >= 32 ? 32 : FLEN;

    typedef struct packed {
        logic [11:0] offset;
        logic [2:0] fn3;
        logic fp;
        logic double;
        logic amo;
        amo_t amo_type;
        logic [31:0] amo_wdata;
        id_t id;
        logic store_collision;
        logic [LOG2_SQ_DEPTH-1:0] sq_index;
    } lq_entry_t;

    typedef struct packed {
        logic discard;
        logic [19:0] addr;
        ls_subunit_t subunit;
    } addr_entry_t;

    logic [LOG2_SQ_DEPTH-1:0] sq_index;
    logic [LOG2_SQ_DEPTH-1:0] sq_oldest;
    addr_hash_t addr_hash;
    logic potential_store_conflict;

    logic lq_addr_discard;
    logic sq_addr_discard;

    logic load_blocked;
    logic load_pop;
    logic load_addr_bit_3;
    logic [2:0] load_fn3;
    fp_ls_op_t load_type;
    logic store_pop;
    logic store_addr_bit_3;
    logic [31:0] store_data;

    fifo_interface #(.DATA_TYPE(lq_entry_t)) lq();
    fifo_interface #(.DATA_TYPE(addr_entry_t)) lq_addr();
    store_queue_interface sq();
    fifo_interface #(.DATA_TYPE(addr_entry_t)) sq_addr();
    ////////////////////////////////////////////////////
    //Implementation

    //Can accept requests so long as store queue is not full
    //To allow additional loads with a full store queue would require
    //extra logic to handle the case where there is a collision and the
    //sq is full
    assign lsq.full = sq.full;
    
    //Address hash for load-store collision checking
    addr_hash #(.USE_BIT_3(~CONFIG.INCLUDE_UNIT.FPU))
    lsq_addr_hash (
        .addr (lsq.data_in.offset),
        .addr_hash (addr_hash)
    );

    ////////////////////////////////////////////////////
    //Load Queue
    cva5_fifo #(.DATA_TYPE(lq_entry_t), .FIFO_DEPTH(MAX_IDS))
    load_queue_fifo (
        .clk(clk),
        .rst(rst),
        .fifo(lq)
    );
    cva5_fifo #(.DATA_TYPE(addr_entry_t), .FIFO_DEPTH(MAX_IDS))
    load_queue_addr_fifo (
        .clk(clk),
        .rst(rst),
        .fifo(lq_addr)
    );

    //FIFO control signals
    assign lq.push = lsq.push & lsq.data_in.load;
    assign lq.potential_push = lsq.potential_push;
    assign lq.pop = load_pop | lq_addr_discard;

    assign lq_addr.push = lsq.addr_push & lsq.addr_data_in.rnw;
    assign lq_addr.potential_push = lq_addr.push;
    assign lq_addr.data_in.addr = lsq.addr_data_in.addr;
    assign lq_addr.data_in.subunit = lsq.addr_data_in.subunit;
    assign lq_addr.data_in.discard = lsq.addr_data_in.discard;
    assign lq_addr.pop = load_pop | lq_addr_discard;

    assign lq_addr_discard = lq_addr.valid ? lq_addr.data_out.discard : lsq.addr_push & lsq.addr_data_in.rnw & lsq.addr_data_in.discard;

    //FIFO data ports
    assign lq.data_in = '{
        offset : lsq.data_in.offset,
        fn3 : lsq.data_in.fn3,
        fp : lsq.data_in.fp,
        double : lsq.data_in.double,
        amo : lsq.data_in.amo,
        amo_type : lsq.data_in.amo_type,
        amo_wdata : lsq.data_in.data,
        id : lsq.data_in.id, 
        store_collision : potential_store_conflict | (CONFIG.INCLUDE_AMO & lsq.data_in.amo), //Collision forces sequential consistence
        sq_index : sq_index
    };
    ////////////////////////////////////////////////////
    //Store Queue
    assign sq.push = lsq.push & (lsq.data_in.store | lsq.data_in.cache_op);
    assign sq.pop = store_pop | sq_addr_discard;
    assign sq.data_in = lsq.data_in;

    store_queue  # (.CONFIG(CONFIG)) sq_block (
        .clk (clk),
        .rst (rst),
        .sq (sq),
        .store_forward_wb_group (store_forward_wb_group),
        .fp_store_forward_wb_group (fp_store_forward_wb_group),
        .addr_hash (addr_hash),
        .potential_store_conflict (potential_store_conflict),
        .sq_index (sq_index),
        .sq_oldest (sq_oldest),
        .wb_packet (wb_packet),
        .fp_wb_packet (fp_wb_packet),
        .store_retire (store_retire)
    );
    cva5_fifo #(.DATA_TYPE(addr_entry_t), .FIFO_DEPTH(CONFIG.SQ_DEPTH))
    store_queue_addr_fifo (
        .clk(clk),
        .rst(rst),
        .fifo(sq_addr)
    );

    assign sq_addr.push = lsq.addr_push & ~lsq.addr_data_in.rnw;
    assign sq_addr.potential_push = sq_addr.push;
    assign sq_addr.data_in.addr = lsq.addr_data_in.addr;
    assign sq_addr.data_in.subunit = lsq.addr_data_in.subunit;
    assign sq_addr.data_in.discard = lsq.addr_data_in.discard;
    assign sq_addr.pop = store_pop | sq_addr_discard;

    assign sq_addr_discard = sq.valid & (~lq.valid | load_blocked) & (sq_addr.valid ? sq_addr.data_out.discard : lsq.addr_push & ~lsq.addr_data_in.rnw & lsq.addr_data_in.discard);


    ////////////////////////////////////////////////////
    //Output
    //Priority is for loads over stores.
    //A store will be selected only if no loads are ready

    generate
    if (CONFIG.INCLUDE_UNIT.FPU) begin : gen_fpu_split
        if (FLEN > 32) begin : gen_load_split
            //Double precision loads are done across two cycles, higher word first
            logic load_p2;
            logic load_fp_hold;

            assign load_fp_hold = ~load_p2 & lq.data_out.double;
            assign load_pop = lsq.load_pop & ~load_fp_hold;
            assign load_addr_bit_3 = load_fp_hold | lq.data_out.offset[2];
            assign load_fn3 = lq.data_out.fp ? LS_W_fn3 : lq.data_out.fn3;
           
            always_comb begin
                if (~lq.data_out.fp)
                    load_type = INT_DONE;
                else if (~lq.data_out.double)
                    load_type = SINGLE_DONE;
                else if (load_p2)
                    load_type = DOUBLE_DONE;
                else
                    load_type = DOUBLE_HOLD;
            end

            always_ff @(posedge clk) begin
                if (rst)
                    load_p2 <= 0;
                else if (lsq.load_pop)
                    load_p2 <= load_fp_hold;
                end
        end else begin : gen_no_load_split
            //All loads are single cycle (load only the upper word)
            assign load_pop = lsq.load_pop;
            assign load_addr_bit_3 = lq.data_out.offset[2] | lq.data_out.double;
            assign load_fn3 = lq.data_out.fp ? LS_W_fn3 : lq.data_out.fn3;
            always_comb begin
                if (lq.data_out.double)
                    load_type = DOUBLE_DONE;
                else if (lq.data_out.fp)
                    load_type = SINGLE_DONE;
                else
                    load_type = INT_DONE;
            end
        end

        ////////////////////////////////////////////////////
        //Stores
        //Mux between integer stores, single precision stores, and double precision stores
        //Double precision stores take 2 cycles, with the lowest 32 bits on the first cycle (even if FLEN <= 32)
        //This is because some functions load double-precision data as integers and operate on them
        //Therefore, reduced FP numbers must be stored as if they were full size
        logic store_p2;
        logic store_fp_hold;

        assign store_fp_hold = ~store_p2 & sq.data_out.double;
        assign store_pop = lsq.store_pop & ~store_fp_hold;
        assign store_addr_bit_3 = sq.data_out.double ? store_p2 : sq.data_out.offset[2]; 

        always_ff @(posedge clk) begin
            if (rst)
                store_p2 <= 0;
            else if (lsq.store_pop)
                store_p2 <= store_fp_hold;
        end

        always_comb begin
            store_data = '0;
            if (sq.data_out.fp & ~sq.data_out.double) //Store single in upper bits
                store_data[31-:FLEN_F] = sq.data_out.fp_data[FLEN_F-1:0];
            else if (store_fp_hold) //First cycle of double - store lower bits (may just be 0)
                store_data = 32'(sq.data_out.fp_data[DOUBLE_MIN_WIDTH-1:0]) << 64-FLEN;
            else if (store_p2) //Second cycle of double - store upper bits
                store_data[31-:DOUBLE_MIN_WIDTH] = sq.data_out.fp_data[FLEN-1-:DOUBLE_MIN_WIDTH];
            else //Not FP
                store_data = sq.data_out.data;
        end
    end else begin : gen_no_fpu
        //Plain integer memory operations
        assign load_pop = lsq.load_pop;
        assign load_addr_bit_3 = lq.data_out.offset[2];
        assign load_fn3 = lq.data_out.fn3;
        assign load_type = INT_DONE;
        assign store_pop = lsq.store_pop;
        assign store_addr_bit_3 = sq.data_out.offset[2];
        assign store_data = sq.data_out.data;
    end
    endgenerate

    assign load_blocked = (lq.data_out.store_collision & (lq.data_out.sq_index != sq_oldest));

    //Requests are only valid if the TLB has returned the physical address and there was no exception
    assign lsq.load_valid = lq.valid & ~load_blocked & (lq_addr.valid ? ~lq_addr.data_out.discard : lsq.addr_push & lsq.addr_data_in.rnw & ~lsq.addr_data_in.discard);
    assign lsq.store_valid = sq.valid & (sq_addr.valid ? ~sq_addr.data_out.discard : lsq.addr_push & ~lsq.addr_data_in.rnw & ~lsq.addr_data_in.discard);

    assign lsq.load_data_out = '{
        addr : {(lq_addr.valid ? lq_addr.data_out.addr : lsq.addr_data_in.addr), lq.data_out.offset[11:3], load_addr_bit_3, lq.data_out.offset[1:0]},
        load : 1,
        store : 0,
        cache_op : 0,
        amo : lq.data_out.amo,
        amo_type : lq.data_out.amo_type,
        be : '1,
        fn3 : load_fn3,
        subunit : lq_addr.valid ? lq_addr.data_out.subunit : lsq.addr_data_in.subunit,
        data_in : CONFIG.INCLUDE_AMO ? lq.data_out.amo_wdata : 'x,
        id : lq.data_out.id,
        fp_op : load_type
    };

    assign lsq.store_data_out = '{
        addr : {(sq_addr.valid ? sq_addr.data_out.addr : lsq.addr_data_in.addr), sq.data_out.offset[11:3], store_addr_bit_3, sq.data_out.offset[1:0]},
        load : 0,
        store : 1,
        cache_op : sq.data_out.cache_op,
        amo : 0,
        amo_type : amo_t'('x),
        be : sq.data_out.be,
        fn3 : 'x,
        subunit : sq_addr.valid ? sq_addr.data_out.subunit : lsq.addr_data_in.subunit,
        data_in : store_data,
        id : 'x,
        fp_op : fp_ls_op_t'('x)
    };

    assign lsq.sq_empty = sq.empty;
    assign lsq.empty = ~lq.valid & sq.empty;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
