/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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

module icache

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
        input logic icache_on,
        l1_arbiter_request_interface.master l1_request,
        l1_arbiter_return_interface.master l1_response,

        memory_sub_unit_interface.responder fetch_sub
    );

    localparam derived_cache_config_t SCONFIG = get_derived_cache_params(CONFIG, CONFIG.ICACHE, CONFIG.ICACHE_ADDR);
    localparam bit [SCONFIG.SUB_LINE_ADDR_W-1:0] END_OF_LINE_COUNT = SCONFIG.SUB_LINE_ADDR_W'(CONFIG.ICACHE.LINE_W-1);

    cache_functions_interface #(.TAG_W(SCONFIG.TAG_W), .LINE_W(SCONFIG.LINE_ADDR_W), .SUB_LINE_W(SCONFIG.SUB_LINE_ADDR_W)) addr_utils();

    logic tag_hit;
    logic [CONFIG.ICACHE.WAYS-1:0] tag_hit_way;

    logic tag_update;
    logic [CONFIG.ICACHE.WAYS-1:0] replacement_way;
    logic [CONFIG.ICACHE.WAYS-1:0] tag_update_way;

    logic [SCONFIG.SUB_LINE_ADDR_W-1:0] word_count;
    logic [SCONFIG.SUB_LINE_ADDR_W-1:0] target_word;
    logic is_target_word;

    logic line_complete;

    logic [31:0] data_out [CONFIG.ICACHE.WAYS-1:0];

    logic linefill_in_progress;
    logic request_in_progress;

    logic miss_data_valid;
    logic second_cycle;
    logic [31:0] second_cycle_addr;

    fifo_interface #(.DATA_WIDTH(32)) input_fifo();

    logic new_request;
    logic [31:0] new_request_addr;
    ////////////////////////////////////////////////////
    //Implementation

    //On a new request, the tag and data banks are accessed
    //On the second cycle of a request hit/miss determination is performed
    //On a miss, the memory request starts on the third cycle

    assign new_request = (fetch_sub.new_request | input_fifo.valid) & ((~request_in_progress | tag_hit) & ~linefill_in_progress);

    assign input_fifo.push = fetch_sub.new_request & (~new_request | input_fifo.valid);
    assign input_fifo.potential_push = input_fifo.push;
    assign input_fifo.pop = new_request & input_fifo.valid;
    assign input_fifo.data_in = fetch_sub.addr;

    assign new_request_addr = input_fifo.valid ? input_fifo.data_out : fetch_sub.addr;

    cva5_fifo #(.DATA_WIDTH(32), .FIFO_DEPTH(2))
    cache_input_fifo (
        .clk (clk), 
        .rst (rst), 
        .fifo (input_fifo)
    );
    ////////////////////////////////////////////////////
    //Ready determination
    always_ff @ (posedge clk) begin
        if (rst)
            request_in_progress <= 0;
        else
            request_in_progress <= (request_in_progress & ~fetch_sub.data_valid) | new_request;
    end

    assign fetch_sub.ready = ~input_fifo.full;

    ////////////////////////////////////////////////////
    //General Control Logic
    always_ff @ (posedge clk) begin
        if (rst)
            second_cycle <= 0;
        else
            second_cycle <= new_request;
    end

    always_ff @(posedge clk) begin
        if (new_request)
            second_cycle_addr <= new_request_addr;
    end

    //As request can be aborted on any cycle, only update tags if memory request is in progress
    always_ff @ (posedge clk) begin
        if (rst)
            tag_update <= 0;
        else
            tag_update <= l1_request.ack;
    end

    //Replacement policy is psuedo random
    cycler #(CONFIG.ICACHE.WAYS) replacement_policy (
        .clk (clk), 
        .rst (rst), 
        .en (1'b1), 
        .one_hot (replacement_way)
    );
    always_ff @ (posedge clk) begin
        if (second_cycle & ~linefill_in_progress)
            tag_update_way <= replacement_way;
    end

    ////////////////////////////////////////////////////
    //L1 arbiter request
    logic initiate_l1_request;
    logic request_r;

    assign l1_request.addr = second_cycle_addr;
    assign l1_request.data = 0;
    assign l1_request.rnw = 1;
    assign l1_request.be = 0;
    assign l1_request.size = 5'(CONFIG.ICACHE.LINE_W-1);
    assign l1_request.is_amo = 0;
    assign l1_request.amo = 0;

    assign initiate_l1_request = second_cycle & (~tag_hit | ~icache_on);
    always_ff @ (posedge clk) begin
        if (rst)
            request_r <= 0;
        else
            request_r <= (initiate_l1_request | request_r) & ~l1_request.ack;
    end
    assign l1_request.request = request_r;

    ////////////////////////////////////////////////////
    //Miss state tracking
    always_ff @ (posedge clk) begin
        if (rst)
            linefill_in_progress <= 0;
        else
            linefill_in_progress <= (linefill_in_progress & ~line_complete) | l1_request.ack;
    end

    ////////////////////////////////////////////////////
    //Tag banks
    itag_banks #(.CONFIG(CONFIG), .SCONFIG(SCONFIG))
    icache_tag_banks (
        .clk(clk),
        .rst(rst), //clears the read_hit_allowed flag
        .stage1_line_addr(addr_utils.getTagLineAddr(new_request_addr)),
        .stage2_line_addr(addr_utils.getTagLineAddr(second_cycle_addr)),
        .stage2_tag(addr_utils.getTag(second_cycle_addr)),
        .update_way(tag_update_way),
        .update(tag_update),
        .stage1_adv(new_request & icache_on),
        .tag_hit(tag_hit),
        .tag_hit_way(tag_hit_way)
    );

    ////////////////////////////////////////////////////
    //Data Banks
    genvar i;
    generate for (i=0; i < CONFIG.ICACHE.WAYS; i++) begin : idata_bank_gen
        byte_en_BRAM #(CONFIG.ICACHE.LINES*CONFIG.ICACHE.LINE_W) idata_bank (
            .clk(clk),
            .addr_a(addr_utils.getDataLineAddr(new_request_addr)),
            .addr_b(addr_utils.getDataLineAddr({second_cycle_addr[31:SCONFIG.SUB_LINE_ADDR_W+2], word_count, 2'b0})),
            .en_a(new_request),
            .en_b(tag_update_way[i] & l1_response.data_valid),
            .be_a('0),
            .be_b('1),
            .data_in_a('0),
            .data_in_b(l1_response.data),
            .data_out_a(data_out[i]),
            .data_out_b()
        );
    end endgenerate

    ////////////////////////////////////////////////////
    //Miss data path
    assign target_word = second_cycle_addr[2 +: SCONFIG.SUB_LINE_ADDR_W];
    assign is_target_word = (target_word == word_count);

    always_ff @ (posedge clk) begin
        if (rst)
            word_count <= 0;
        else
            word_count <= word_count + SCONFIG.SUB_LINE_ADDR_W'(l1_response.data_valid);
    end

    assign miss_data_valid = request_in_progress & l1_response.data_valid & is_target_word;
    assign line_complete = l1_response.data_valid & (word_count == END_OF_LINE_COUNT);

    ////////////////////////////////////////////////////
    //Output muxing
    localparam OMUX_W = CONFIG.ICACHE.WAYS+1;
    logic [OMUX_W-1:0] priority_vector;
    logic [$clog2(OMUX_W)-1:0] output_sel;
    logic [31:0] output_array [OMUX_W];
    always_comb begin
        priority_vector[0] = miss_data_valid;
        output_array[0] = l1_response.data;
        for (int i = 0; i < CONFIG.ICACHE.WAYS; i++) begin
            priority_vector[i+1] = tag_hit_way[i];
            output_array[i+1] = data_out[i];
        end
    end
    priority_encoder #(.WIDTH(OMUX_W))
    arb_encoder
    (
        .priority_vector (priority_vector),
        .encoded_result (output_sel)
    );
    assign fetch_sub.data_out = output_array[output_sel];
    assign fetch_sub.data_valid = miss_data_valid | tag_hit;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    icache_l1_arb_ack_assertion:
        assert property (@(posedge clk) disable iff (rst) l1_request.ack |-> l1_request.request)
        else $error("Spurious icache ack received from arbiter!");

    icache_l1_arb_data_valid_assertion:
        assert property (@(posedge clk) disable iff (rst) l1_response.data_valid |-> linefill_in_progress)
        else $error("Spurious icache data received from arbiter!");

endmodule
