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

import taiga_config::*;
import taiga_types::*;

module icache(
        input logic clk,
        input logic rst,
        input logic icache_on,
        l1_arbiter_request_interface.master l1_request,
        l1_arbiter_return_interface.master l1_response,

        fetch_sub_unit_interface.sub_unit fetch_sub
        );

    logic tag_hit;
    logic [ICACHE_WAYS-1:0] tag_hit_way;

    logic tag_update;
    logic [ICACHE_WAYS-1:0] replacement_way;
    logic [ICACHE_WAYS-1:0] tag_update_way;

    logic [$clog2(ICACHE_LINE_W)-1:0] word_count;
    logic is_target_word;
    logic line_complete;

    logic [31:0] data_out [ICACHE_WAYS-1:0];
    logic [31:0] miss_data;

    logic miss_data_ready;
    logic second_cycle;

    logic idle;
    logic memory_complete;
    logic hit_allowed;

    /*************************************
     * General Control Logic
     *************************************/

    always_ff @ (posedge clk) begin
        if (rst | fetch_sub.flush)
            second_cycle <= 0;
        else
            second_cycle <= fetch_sub.new_request;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            tag_update <= 0;
        else if (second_cycle)
            tag_update <= icache_on  & ~tag_hit;        //Cache enabled, read miss
        else
            tag_update <= 0;
    end

    /*************************************
     * L1 Arbiter Interface
     *************************************/
    assign l1_request.addr = fetch_sub.stage2_addr;
    assign l1_request.data = 0;
    assign l1_request.rnw = 1;
    assign l1_request.be = 0;
    assign l1_request.size = (ICACHE_LINE_W-1);
    assign l1_request.is_amo = 0;
    assign l1_request.amo = 0;

    always_ff @ (posedge clk) begin
        if (rst)
            word_count <= 0;
        else if (l1_response.data_valid)
            word_count <= word_count + 1;
    end

    //request registered
    always_ff @ (posedge clk) begin
        if (rst)
            l1_request.request <= 0;
        else if (second_cycle)
            l1_request.request <= ~tag_hit | ~icache_on;
        else if (l1_request.ack)
            l1_request.request <= 0;
    end


    /*************************************
     * Cache Components
     *************************************/
    //Free running one hot cycler.
    cycler #(ICACHE_WAYS) replacement_policy (.*, .en(1'b1), .one_hot(replacement_way));

    always_ff @ (posedge clk) begin
        if (second_cycle) begin
            tag_update_way<= replacement_way;
        end
    end

    //Tag banks
    itag_banks icache_tag_banks (.*,
            .stage1_addr(fetch_sub.stage1_addr),
            .stage2_addr(fetch_sub.stage2_addr),
            .update_way(tag_update_way),
            .update(tag_update),
            .stage1_adv(fetch_sub.new_request & icache_on)
        );

    //Data Banks
    genvar i;
    generate
        for (i=0; i < ICACHE_WAYS; i++) begin : idata_bank_gen
            byte_en_BRAM #(ICACHE_LINES*ICACHE_LINE_W) idata_bank (
                    .clk(clk),
                    .addr_a(fetch_sub.stage1_addr[ICACHE_LINE_ADDR_W+ICACHE_SUB_LINE_ADDR_W+2-1:2]),
                    .addr_b({fetch_sub.stage2_addr[ICACHE_LINE_ADDR_W+ICACHE_SUB_LINE_ADDR_W+2-1:ICACHE_SUB_LINE_ADDR_W+2], word_count}),
                    .en_a(fetch_sub.new_request),
                    .en_b(tag_update_way[i] & l1_response.data_valid),
                    .be_a('0),
                    .be_b('1),
                    .data_in_a('0),
                    .data_in_b(l1_response.data),
                    .data_out_a(data_out[i]),
                    .data_out_b()
                );
        end
    endgenerate

    /*************************************
     * Output Muxing
     *************************************/
    assign is_target_word = (fetch_sub.stage2_addr[ICACHE_SUB_LINE_ADDR_W+1:2] == word_count);

    always_ff @ (posedge clk) begin
        if (l1_response.data_valid & is_target_word)
            miss_data <= l1_response.data;
        else
            miss_data <= 0;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            miss_data_ready <= 0;
        else
            miss_data_ready <= l1_response.data_valid & is_target_word;
    end


    always_comb begin
        fetch_sub.data_out = miss_data;//zero if not a miss
        for (int i =0; i < ICACHE_WAYS; i++) begin
            fetch_sub.data_out = fetch_sub.data_out | (data_out[i] & {32{tag_hit_way[i]}});
        end
    end

    assign fetch_sub.data_valid = miss_data_ready | tag_hit;

    /*************************************
     * Pipeline Advancement
     *************************************/
    assign  line_complete = (l1_response.data_valid && (word_count == (ICACHE_LINE_W-1)));

    always_ff @ (posedge clk) begin
        if (rst)
            memory_complete <= 0;
        else
            memory_complete <= line_complete;
    end

    assign fetch_sub.ready = tag_hit | memory_complete | idle;//~(second_cycle & ~tag_hit) & ~miss;

    always_ff @ (posedge clk) begin
        if (rst)
            idle <= 1;
        else if (fetch_sub.new_request & ~fetch_sub.flush)
            idle <= 0;
        else if (memory_complete | tag_hit) //read miss OR write through complete
            idle <= 1;
    end


endmodule
