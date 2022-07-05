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

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )
    (
        input logic clk,
        input logic rst,
        input gc_outputs_t gc,

        load_store_queue_interface.queue lsq,
        //Writeback snooping
        input wb_packet_t wb_snoop,

        //Retire release
        input id_t retire_ids [RETIRE_PORTS],
        input logic retire_port_valid [RETIRE_PORTS]
    );

    typedef struct packed {
        logic [31:0] addr;
        logic [2:0] fn3;
        id_t id;
        phys_addr_t phys_addr;
        logic [CONFIG.SQ_DEPTH-1:0] potential_store_conflicts;
    } lq_entry_t;

    addr_hash_t addr_hash;
    logic [CONFIG.SQ_DEPTH-1:0] potential_store_conflicts;
    sq_entry_t sq_entry;
    logic store_conflict;

    lq_entry_t lq_data_in;
    lq_entry_t lq_data_out;

    fifo_interface #(.DATA_WIDTH($bits(lq_entry_t))) lq();
    store_queue_interface sq();
    ////////////////////////////////////////////////////
    //Implementation

    //Can accept requests so long as store queue is not needed or is not full
    assign lsq.full = lsq.data_in.store & sq.full;
    
    //Address hash for load-store collision checking
    addr_hash lsq_addr_hash (
        .clk (clk),
        .rst (rst | gc.sq_flush),
        .addr (lsq.data_in.addr),
        .addr_hash (addr_hash)
    );

    ////////////////////////////////////////////////////
    //Load Queue
    cva5_fifo #(.DATA_WIDTH($bits(lq_entry_t)), .FIFO_DEPTH(MAX_IDS))
    load_queue_fifo (
        .clk(clk),
        .rst(rst),
        .fifo(lq)
    );

    //FIFO control signals
    assign lq.push = lsq.push & lsq.data_in.load;
    assign lq.potential_push = lsq.potential_push;
    assign lq.pop = lsq.load_pop;

    //FIFO data ports
    assign lq_data_in = '{
        addr : lsq.data_in.addr,
        fn3 : lsq.data_in.fn3,
        id : lsq.data_in.id, 
        phys_addr : lsq.data_in.phys_addr,
        potential_store_conflicts : potential_store_conflicts
    };
    assign lq.data_in = lq_data_in;
    assign lq_data_out = lq.data_out;
    ////////////////////////////////////////////////////
    //Store Queue
    assign sq.push = lsq.push &  lsq.data_in.store;
    assign sq.pop = lsq.store_pop;
    assign sq.data_in = lsq.data_in;

    store_queue  # (.CONFIG(CONFIG)) sq_block (
        .clk (clk),
        .rst (rst | gc.sq_flush),
        .lq_push (lq.push),
        .lq_pop (lq.pop),
        .sq (sq),
        .addr_hash (addr_hash),
        .potential_store_conflicts (potential_store_conflicts),
        .prev_store_conflicts (lq_data_out.potential_store_conflicts),
        .store_conflict (store_conflict),
        .wb_snoop (wb_snoop),
        .retire_ids (retire_ids),
        .retire_port_valid (retire_port_valid)
    );

    ////////////////////////////////////////////////////
    //Output
    //Priority is for loads over stores.
    //A store will be selected only if either no loads are ready, OR if the store queue is full and a store is ready
    assign lsq.load_valid = lq.valid & ~store_conflict;
    assign lsq.store_valid = sq.valid;

    assign lsq.load_data_out = '{
        addr : lq_data_out.addr,
        load : 1,
        store : 0,
        be : '0,
        fn3 : lq_data_out.fn3,
        data_in : sq.data_out.data,
        id : lq_data_out.id,
        phys_addr : lq_data_out.phys_addr
    };

    assign lsq.store_data_out = '{
        addr : sq.data_out.addr,
        load : 0,
        store : 1,
        be : sq.data_out.be,
        fn3 : sq.data_out.fn3,
        data_in : sq.data_out.data,
        id : lq_data_out.id,
        phys_addr : lq_data_out.phys_addr
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
