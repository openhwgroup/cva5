/*
 * Copyright © 2022 Eric Matthews
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

module dcache

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )
    (
        input logic clk,
        input logic rst,
        input logic dcache_on,
        l1_arbiter_request_interface.master l1_request,
        l1_arbiter_return_interface.master l1_response,
        input logic sc_complete,
        input logic sc_success,
        input logic clear_reservation,
        input amo_details_t amo,
        input logic uncacheable_load,
        input logic uncacheable_store,
        input logic is_load,
        input logic load_request,
        input logic store_request,
        output logic load_ready,
        output logic store_ready,
        input data_access_shared_inputs_t ls_load,
        input data_access_shared_inputs_t ls_store,
        memory_sub_unit_interface.responder ls
    );

    localparam derived_cache_config_t SCONFIG = get_derived_cache_params(CONFIG, CONFIG.DCACHE, CONFIG.DCACHE_ADDR);
    localparam LOG2_WAYS = (CONFIG.DCACHE.WAYS == 1) ? 1 : $clog2(CONFIG.DCACHE.WAYS);

    localparam bit [SCONFIG.SUB_LINE_ADDR_W-1:0] END_OF_LINE_COUNT = SCONFIG.SUB_LINE_ADDR_W'(CONFIG.DCACHE.LINE_W-1);

    cache_functions_interface # (.LINE_W(SCONFIG.LINE_ADDR_W), .SUB_LINE_W(SCONFIG.SUB_LINE_ADDR_W)) addr_utils ();

    typedef struct packed{
        logic [31:0] addr;
        logic uncacheable;
    } load_stage2_t;
    load_stage2_t stage2_load;

    typedef struct packed{
        logic [31:0] addr;
        logic [3:0] be;
        logic [31:0] data;
        logic uncacheable;
    } store_stage2_t;
    store_stage2_t stage2_store;

    logic [CONFIG.DCACHE.WAYS-1:0] load_tag_hit_way;
    logic [CONFIG.DCACHE.WAYS-1:0] store_tag_hit_way;

    logic [CONFIG.DCACHE.WAYS-1:0] replacement_way;
    logic [CONFIG.DCACHE.WAYS-1:0] replacement_way_r;

    logic load_tag_check;
    logic load_hit;
    logic store_hit;
    logic [LOG2_WAYS-1:0] tag_hit_index;
    logic [LOG2_WAYS-1:0] replacement_index;
    logic [LOG2_WAYS-1:0] replacement_index_r;
    logic [LOG2_WAYS-1:0] load_sel;

    logic is_target_word;
    logic [SCONFIG.SUB_LINE_ADDR_W-1:0] word_count;
    logic miss_data_valid;
    logic line_complete;

    logic arb_load_sel;
    logic load_l1_arb_ack;
    logic store_l1_arb_ack;

    logic [31:0] ram_load_data [CONFIG.DCACHE.WAYS-1:0];

    typedef enum {
        LOAD_IDLE = 0,
        LOAD_HIT_CHECK = 1,
        LOAD_L1_REQUEST = 2,
        LOAD_FILL = 3
    } load_path_enum_t;
    logic [3:0] load_state, load_state_next;

    typedef enum {
        STORE_IDLE = 0,
        STORE_L1_REQUEST = 1
    } store_path_enum_t;
    logic [1:0] store_state, store_state_next;

    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Load Path
    always_ff @ (posedge clk) begin
        if (rst) begin
            load_state <= 0;
            load_state[LOAD_IDLE] <= 1;
        end
        else
            load_state <= load_state_next;
    end

    always_comb begin
        load_state_next[LOAD_IDLE] = (load_state[LOAD_IDLE] & ~load_request) | ((load_hit & ~load_request) | line_complete);
        load_state_next[LOAD_HIT_CHECK] = load_request;
        load_state_next[LOAD_L1_REQUEST] = (load_state[LOAD_L1_REQUEST] & ~load_l1_arb_ack) | (load_state[LOAD_HIT_CHECK] & ~load_hit);
        load_state_next[LOAD_FILL] = (load_state[LOAD_FILL] & ~line_complete) | (load_state[LOAD_L1_REQUEST] & load_l1_arb_ack);
    end

    assign load_ready = (load_state[LOAD_IDLE] | load_hit) & (store_state[STORE_IDLE]);

    always_ff @ (posedge clk) begin
        if (load_request) begin
            stage2_load.addr <= ls_load.addr;
            stage2_load.uncacheable <= uncacheable_load;
        end
    end

    assign load_tag_check = load_request & dcache_on & ~uncacheable_load;

    ////////////////////////////////////////////////////
    //Load Miss
    always_ff @ (posedge clk) begin
        if (load_request)
            word_count <= 0;
        else
            word_count <= word_count + SCONFIG.SUB_LINE_ADDR_W'(l1_response.data_valid);
    end
    assign is_target_word = (stage2_load.addr[2 +: SCONFIG.SUB_LINE_ADDR_W] == word_count) | stage2_load.uncacheable;

    assign line_complete = l1_response.data_valid & ((word_count == END_OF_LINE_COUNT) | stage2_load.uncacheable);

    ////////////////////////////////////////////////////
    //Store Path
    always_ff @ (posedge clk) begin
        if (rst) begin
            store_state <= 0;
            store_state[STORE_IDLE] <= 1;
        end
        else
            store_state <= store_state_next;
    end

    always_comb begin
        store_state_next[STORE_IDLE] = (store_state[STORE_IDLE] & ~store_request) | (store_l1_arb_ack & ~store_request);
        store_state_next[STORE_L1_REQUEST] = (store_state[STORE_L1_REQUEST] & ~store_l1_arb_ack) | store_request;
    end
    assign store_ready = (store_state[STORE_IDLE] | store_l1_arb_ack) & (load_state[LOAD_IDLE] | load_hit);

    assign ls.ready = is_load ? load_ready : store_ready;

    always_ff @ (posedge clk) begin
        if (store_request) begin
            stage2_store.addr <= ls_store.addr;
            stage2_store.uncacheable <= uncacheable_store;
            stage2_store.be <= ls_store.be;
            stage2_store.data <= ls_store.data_in;
        end
    end

    ////////////////////////////////////////////////////
    //L1 Arbiter Interface
    //Priority to oldest request
    fifo_interface #(.DATA_WIDTH(1)) request_order();

    assign request_order.data_in = load_request;
    assign request_order.push = load_request | store_request;
    assign request_order.potential_push = request_order.push;

    assign request_order.pop = l1_request.ack | load_hit;

    cva5_fifo #(.DATA_WIDTH(1), .FIFO_DEPTH(2))
    request_order_fifo (
        .clk (clk),
        .rst (rst), 
        .fifo (request_order)
    );

    assign arb_load_sel = request_order.data_out;
    
    assign l1_request.addr = arb_load_sel ? stage2_load.addr : stage2_store.addr;//Memory interface aligns request to burst size (done there to support AMO line-read word-write)
    assign l1_request.data = stage2_store.data;
    assign l1_request.rnw = arb_load_sel;
    assign l1_request.be = stage2_store.be;
    assign l1_request.size = (arb_load_sel & ~stage2_load.uncacheable) ? 5'(CONFIG.DCACHE.LINE_W-1) : 0;//LR and AMO ops are included in load
    assign l1_request.is_amo = 0;
    assign l1_request.amo = 0;

    assign l1_request.request = load_state[LOAD_L1_REQUEST] | store_state[STORE_L1_REQUEST];

    assign load_l1_arb_ack = l1_request.ack & arb_load_sel;
    assign store_l1_arb_ack = l1_request.ack & ~arb_load_sel;
    ////////////////////////////////////////////////////
    //Replacement policy (free runing one-hot cycler, i.e. pseudo random)
    cycler #(CONFIG.DCACHE.WAYS) replacement_policy (
        .clk (clk), 
        .rst (rst), 
        .en (1'b1), 
        .one_hot (replacement_way)
    );

    ////////////////////////////////////////////////////
    //Tag banks
    dcache_tag_banks #(.CONFIG(CONFIG), .SCONFIG(SCONFIG))
    tag_banks (
        .clk (clk),
        .rst (rst),
        .load_addr (ls_load.addr),
        .load_req (load_tag_check),
        .miss_addr (stage2_load.addr),
        .miss_req (load_l1_arb_ack),
        .miss_way (replacement_way),
        .inv_addr ({l1_response.inv_addr, 2'b0}),
        .extern_inv (l1_response.inv_valid),
        .extern_inv_complete (l1_response.inv_ack),
        .store_addr (ls_store.addr),
        .store_addr_r (stage2_store.addr),
        .store_req (store_request),
        .load_tag_hit (load_hit),
        .load_tag_hit_way (load_tag_hit_way),
        .store_tag_hit (store_hit),
        .store_tag_hit_way (store_tag_hit_way)
    );

    ////////////////////////////////////////////////////
    //Data Bank(s)
    logic [SCONFIG.LINE_ADDR_W+SCONFIG.SUB_LINE_ADDR_W-1:0] data_read_addr;
    assign data_read_addr = load_state[LOAD_FILL] ? {addr_utils.getTagLineAddr(stage2_load.addr), word_count} : addr_utils.getDataLineAddr(ls_load.addr);

    generate for (genvar i=0; i < CONFIG.DCACHE.WAYS; i++) begin : data_bank_gen
        byte_en_BRAM #(CONFIG.DCACHE.LINES*CONFIG.DCACHE.LINE_W) data_bank (
            .clk(clk),
            .addr_a(data_read_addr),
            .addr_b(addr_utils.getDataLineAddr(stage2_store.addr)),
            .en_a(load_tag_check | (replacement_way_r[i] & l1_response.data_valid)),
            .en_b(store_tag_hit_way[i]),
            .be_a({4{(replacement_way_r[i] & l1_response.data_valid)}}),
            .be_b(stage2_store.be),
            .data_in_a(l1_response.data),
            .data_in_b(stage2_store.data),
            .data_out_a(ram_load_data[i]),
            .data_out_b()
        );
    end endgenerate

    ////////////////////////////////////////////////////
    //Output
    //One-hot tag hit / update logic to binary int
    one_hot_to_integer #(CONFIG.DCACHE.WAYS)
    hit_way_conv (
        .one_hot (load_tag_hit_way), 
        .int_out (tag_hit_index)
    );
    one_hot_to_integer #(CONFIG.DCACHE.WAYS)
    replacment_way_conv (
        .one_hot (replacement_way), 
        .int_out (replacement_index)
    );
    always_ff @ (posedge clk) begin
        if (load_l1_arb_ack) begin
            replacement_way_r <= replacement_way;
            replacement_index_r <= replacement_index;
        end
    end

    always_ff @ (posedge clk) miss_data_valid <= l1_response.data_valid & is_target_word;

    assign load_sel = load_state[LOAD_HIT_CHECK] ? tag_hit_index : replacement_index_r;
    assign ls.data_out = ram_load_data[load_sel];
    assign ls.data_valid = load_hit | miss_data_valid;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    dcache_request_when_not_ready_assertion:
        assert property (@(posedge clk) disable iff (rst) load_request |-> load_ready)
        else $error("dcache received request when not ready");

    dache_suprious_l1_ack_assertion:
        assert property (@(posedge clk) disable iff (rst) l1_request.ack |-> (load_state[LOAD_L1_REQUEST] | store_state[STORE_L1_REQUEST]))
        else $error("dcache received ack without a request");

endmodule
