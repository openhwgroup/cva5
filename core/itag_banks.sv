/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 * 
 * This Source Code Form is "Incompatible With Secondary Licenses", as
 * defined by the Mozilla Public License, v. 2.0.
 *
 * Initial code developed under the supervision of Dr. Lesley Shannon,
 * Reconfigurable Computing Lab, Simon Fraser University.
 *
 * Author(s):
 *             Eric Matthews <ematthew@sfu.ca>
 */
 
import taiga_config::*;
import taiga_types::*;

module itag_banks(
        input logic clk,
        input logic rst,

        input logic[31:0] stage1_addr,
        input logic[31:0] stage2_addr,

        input logic[0:ICACHE_WAYS-1] update_way,
        input logic update,

        input logic stage1_adv,

        output tag_hit,
        output logic[0:ICACHE_WAYS-1] tag_hit_way
        );

    typedef logic [ICACHE_TAG_W : 0] itag_entry_t;

    function logic[ICACHE_TAG_W-1:0] getTag(logic[31:0] addr);
        return addr[31 : 32 - ICACHE_TAG_W];
    endfunction

    function logic[ICACHE_LINE_ADDR_W-1:0] getLineAddr(logic[31:0] addr);
        return addr[ICACHE_LINE_ADDR_W + ICACHE_SUB_LINE_ADDR_W + 1 : ICACHE_SUB_LINE_ADDR_W + 2];
    endfunction

    itag_entry_t  tag_line[0:ICACHE_WAYS - 1];

    itag_entry_t stage2_tag;
    assign stage2_tag = {1'b1, getTag(stage2_addr)};

    genvar i;
    generate
        for (i=0; i < ICACHE_WAYS; i=i+1) begin : tag_bank_gen

            tag_bank #(ICACHE_TAG_W+1, ICACHE_LINES) itag_bank (.*,
                    .en_a(stage1_adv), .wen_a('0),
                    .addr_a(getLineAddr(stage1_addr)),
                    .data_in_a('0), .data_out_a(tag_line[i]),

                    .en_b(update), .wen_b(update_way[i]),
                    .addr_b(getLineAddr(stage2_addr)),
                    .data_in_b(stage2_tag), .data_out_b()
                );

            assign tag_hit_way[i] = (stage2_tag == tag_line[i]);

        end
    endgenerate

    assign tag_hit = |tag_hit_way;


endmodule
