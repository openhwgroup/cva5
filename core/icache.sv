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

    logic tag_hit;
    logic [CONFIG.ICACHE.WAYS-1:0] tag_hit_way;

    logic tag_update;
    logic [CONFIG.ICACHE.WAYS-1:0] replacement_way;
    logic [CONFIG.ICACHE.WAYS-1:0] tag_update_way;

    logic [SCONFIG.SUB_LINE_ADDR_W-1:0] word_count;
    logic is_target_word;
    logic line_complete;

    logic [31:0] data_out [CONFIG.ICACHE.WAYS-1:0];
    logic [31:0] miss_data;

    logic miss_in_progress;

    logic miss_data_valid;
    logic second_cycle;
    logic [31:0] second_cycle_addr;

    logic idle;
    logic memory_complete;
    ////////////////////////////////////////////////////
    //Implementation

    //On a new request, the tag and data banks are accessed
    //On the second cycle of a request hit/miss determination is performed
    //On a miss, the memory request starts on the third cycle

    ////////////////////////////////////////////////////
    //General Control Logic
    always_ff @ (posedge clk) begin
        if (rst)
            second_cycle <= 0;
        else
            second_cycle <= fetch_sub.new_request;
    end

    always_ff @(posedge clk) begin
        if (fetch_sub.new_request)
            second_cycle_addr <= fetch_sub.addr;
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
        .clk        (clk), 
        .rst        (rst), 
        .en         (1'b1), 
        .one_hot    (replacement_way)
    );
    always_ff @ (posedge clk) begin
        if (second_cycle)
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
            miss_in_progress <= 0;
        else
            miss_in_progress <= l1_request.ack | (miss_in_progress & ~line_complete);
    end

    ////////////////////////////////////////////////////
    //Tag banks
    itag_banks #(.CONFIG(CONFIG), .SCONFIG(SCONFIG))
    icache_tag_banks (
            .clk(clk),
            .rst(rst), //clears the read_hit_allowed flag
            .stage1_addr(fetch_sub.addr),
            .stage2_addr(second_cycle_addr),
            .update_way(tag_update_way),
            .update(tag_update),
            .stage1_adv(fetch_sub.new_request & icache_on),
            .tag_hit(tag_hit),
            .tag_hit_way(tag_hit_way)
    );

    ////////////////////////////////////////////////////
    //Data Banks
    genvar i;
    generate for (i=0; i < CONFIG.ICACHE.WAYS; i++) begin : idata_bank_gen
        byte_en_BRAM #(CONFIG.ICACHE.LINES*CONFIG.ICACHE.LINE_W) idata_bank (
            .clk(clk),
            .addr_a(fetch_sub.addr[2 +: SCONFIG.LINE_ADDR_W+SCONFIG.SUB_LINE_ADDR_W]),
            .addr_b({second_cycle_addr[(2+SCONFIG.SUB_LINE_ADDR_W) +: SCONFIG.LINE_ADDR_W], word_count}),
            .en_a(fetch_sub.new_request),
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
    always_ff @ (posedge clk) begin
        if (rst)
            word_count <= 0;
        else if (l1_response.data_valid)
            word_count <= word_count + 1;
    end

    assign is_target_word = (second_cycle_addr[2 +: SCONFIG.SUB_LINE_ADDR_W] == word_count);

    always_ff @ (posedge clk) begin
        if (l1_response.data_valid & is_target_word)
            miss_data <= l1_response.data;
        else
            miss_data <= 0;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            miss_data_valid <= 0;
        else
            miss_data_valid <= miss_in_progress & l1_response.data_valid & is_target_word;
    end

    assign  line_complete = (l1_response.data_valid && (word_count == SCONFIG.SUB_LINE_ADDR_W'(CONFIG.ICACHE.LINE_W-1)));
    always_ff @ (posedge clk) begin
        if (rst)
            memory_complete <= 0;
        else
            memory_complete <= line_complete;
    end

    ////////////////////////////////////////////////////
    //Output muxing
    always_comb begin
        fetch_sub.data_out = miss_data;//zero if not a miss
        for (int i = 0; i < CONFIG.ICACHE.WAYS; i++) begin
            fetch_sub.data_out = fetch_sub.data_out | (data_out[i] & {32{tag_hit_way[i]}});
        end
    end

    assign fetch_sub.data_valid = miss_data_valid | tag_hit;

    ////////////////////////////////////////////////////
    //Ready determination
    always_ff @ (posedge clk) begin
        if (rst)
            idle <= 1;
        else if (fetch_sub.new_request)
            idle <= 0;
        else if (memory_complete | tag_hit) //read miss OR write through complete
            idle <= 1;
    end

    assign fetch_sub.ready = tag_hit | memory_complete | idle;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    icache_l1_arb_ack_assertion:
        assert property (@(posedge clk) disable iff (rst) l1_request.ack |-> l1_request.request)
        else $error("Spurious icache ack received from arbiter!");

    icache_l1_arb_data_valid_assertion:
        assert property (@(posedge clk) disable iff (rst) l1_response.data_valid |-> miss_in_progress)
        else $error("Spurious icache data received from arbiter!");

endmodule
