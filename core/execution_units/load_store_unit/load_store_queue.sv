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

    typedef struct packed {
        logic [31:0] addr;
        logic [2:0] fn3;
        logic fp;
        logic double;
        id_t id;
        logic store_collision;
        logic [LOG2_SQ_DEPTH-1:0] sq_index;
    } lq_entry_t;

    logic [LOG2_SQ_DEPTH-1:0] sq_index;
    logic [LOG2_SQ_DEPTH-1:0] sq_oldest;
    addr_hash_t addr_hash;
    logic potential_store_conflict;

    logic load_pop;
    logic load_addr_bit_3;
    logic [2:0] load_fn3;
    logic load_fp_hold;
    logic load_fp_done;
    logic store_pop;
    logic store_addr_bit_3;
    logic [31:0] store_data;

    fifo_interface #(.DATA_TYPE(lq_entry_t)) lq();
    store_queue_interface sq();
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
        .addr (lsq.data_in.addr),
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

    //FIFO control signals
    assign lq.push = lsq.push & lsq.data_in.load;
    assign lq.potential_push = lsq.potential_push;
    assign lq.pop = load_pop;

    //FIFO data ports
    assign lq.data_in = '{
        addr : lsq.data_in.addr,
        fn3 : lsq.data_in.fn3,
        fp : lsq.data_in.fp,
        double : lsq.data_in.double,
        id : lsq.data_in.id, 
        store_collision : potential_store_conflict,
        sq_index : sq_index
    };
    ////////////////////////////////////////////////////
    //Store Queue
    assign sq.push = lsq.push & (lsq.data_in.store | lsq.data_in.cache_op);
    assign sq.pop = store_pop;
    assign sq.data_in = lsq.data_in;

    store_queue  # (.CONFIG(CONFIG)) sq_block (
        .clk (clk),
        .rst (rst | gc.sq_flush),
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

    ////////////////////////////////////////////////////
    //Output
    //Priority is for loads over stores.
    //A store will be selected only if no loads are ready

    generate
    if (CONFIG.INCLUDE_UNIT.FPU && FLEN > 32) begin : gen_fp_split
        //On the first pop of a double, the load/store on the upper 32 bits is done and the request is held
        //The second pop loads/stores the lower 32 bits and actually pops the queue
        //Double precision operations are always aligned on 8 byte boundaries
        logic load_p2;
        logic store_p2;
        logic store_fp_hold;
        logic store_fp_done;
        
        assign load_pop = lsq.load_pop & ~load_fp_hold;
        assign load_addr_bit_3 = load_fp_hold | lq.data_out.addr[2];
        assign load_fn3 = lq.data_out.fp ? LS_W_fn3 : lq.data_out.fn3;
        assign load_fp_hold = ~load_p2 & lq.data_out.double;
        assign load_fp_done = load_p2 | (lq.data_out.fp & ~lq.data_out.double);

        assign store_pop = lsq.store_pop & ~store_fp_hold;
        assign store_addr_bit_3 = store_fp_hold | sq.data_out.addr[2];
        assign store_fp_hold = ~store_p2 & sq.data_out.double;
        assign store_fp_done = store_p2 | (sq.data_out.fp & ~sq.data_out.double);

        always_comb begin
            if (store_fp_hold)
                store_data = {{(64-FLEN){1'b1}}, sq.data_out.fp_data[FLEN-1:32]};
            else if (store_fp_done)
                store_data = sq.data_out.fp_data[31:0];
            else
                store_data = sq.data_out.data;
        end

        always_ff @(posedge clk) begin
            if (rst) begin
                load_p2 <= 0;
                store_p2 <= 0;
            end
            else begin
                if (lsq.load_pop)
                    load_p2 <= load_fp_hold;
                if (lsq.store_pop)
                    store_p2 <= store_fp_hold;
            end
        end

    end else if (CONFIG.INCLUDE_UNIT.FPU && FLEN <= 32) begin : gen_fp_no_split
        //There are FP memory operations but none need to be split
        assign load_pop = lsq.load_pop;
        assign load_addr_bit_3 = lq.data_out.addr[2];
        assign load_fn3 = lq.data_out.fp ? LS_W_fn3 : lq.data_out.fn3;
        assign load_fp_hold = 0;
        assign load_fp_done = lq.data_out.fp;
        assign store_pop = lsq.store_pop;
        assign store_addr_bit_3 = sq.data_out.addr[2];
        assign store_data = sq.data_out.fp ? {{(32-FLEN){1'b1}}, sq.data_out.fp_data} : sq.data_out.data;
    end
    else begin : gen_no_fpu_splitting
        assign load_pop = lsq.load_pop;
        assign load_addr_bit_3 = lq.data_out.addr[2];
        assign load_fn3 = lq.data_out.fn3;
        assign load_fp_hold = 0;
        assign load_fp_done = 0;
        assign store_pop = lsq.store_pop;
        assign store_addr_bit_3 = sq.data_out.addr[2];
        assign store_data = sq.data_out.data;
    end
    endgenerate
    logic load_blocked;
    assign load_blocked = (lq.data_out.store_collision & (lq.data_out.sq_index != sq_oldest));

    assign lsq.load_valid = lq.valid & ~load_blocked;
    assign lsq.store_valid = sq.valid;

    assign lsq.load_data_out = '{
        addr : {lq.data_out.addr[31:3], load_addr_bit_3, lq.data_out.addr[1:0]},
        load : 1,
        store : 0,
        cache_op : 0,
        be : 'x,
        fn3 : load_fn3,
        data_in : 'x,
        id : lq.data_out.id,
        fp_hold : load_fp_hold,
        fp_done : load_fp_done
    };

    assign lsq.store_data_out = '{
        addr : {sq.data_out.addr[31:3], store_addr_bit_3, sq.data_out.addr[1:0]},
        load : 0,
        store : 1,
        cache_op : sq.data_out.cache_op,
        be : sq.data_out.be,
        fn3 : 'x,
        data_in : store_data,
        id : 'x,
        fp_hold : 'x,
        fp_done : 'x
    };

    assign lsq.sq_empty = sq.empty;
    assign lsq.no_released_stores_pending = sq.no_released_stores_pending;
    assign lsq.empty = ~lq.valid & sq.empty;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
