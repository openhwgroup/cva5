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

module itag_banks

    import cva5_config::*;
    import cva5_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG,
        parameter derived_cache_config_t SCONFIG = '{default: 0}
    )

    (
        input logic clk,
        input logic rst,
        input logic ifence,
        input logic[SCONFIG.LINE_ADDR_W-1:0] ifence_addr,

        input logic[SCONFIG.LINE_ADDR_W-1:0] stage1_line_addr,
        input logic[SCONFIG.LINE_ADDR_W-1:0] stage2_line_addr,
        input logic[SCONFIG.TAG_W-1:0] stage2_tag,

        input logic[CONFIG.ICACHE.WAYS-1:0] update_way,
        input logic update,

        input logic stage1_adv,

        output tag_hit,
        output logic[CONFIG.ICACHE.WAYS-1:0] tag_hit_way
        );

    //Valid + tag
    typedef logic [SCONFIG.TAG_W : 0] itag_entry_t;
    itag_entry_t[CONFIG.ICACHE.WAYS-1:0]  tag_line;

    logic hit_allowed;

    always_ff @ (posedge clk) begin
        if (rst)
            hit_allowed <= 0;
        else
            hit_allowed <= stage1_adv;
    end

    sdp_ram_padded #(
        .ADDR_WIDTH(SCONFIG.LINE_ADDR_W),
        .NUM_COL(CONFIG.ICACHE.WAYS),
        .COL_WIDTH(SCONFIG.TAG_W+1),
        .PIPELINE_DEPTH(0)
    ) itag_bank (
        .a_en(update | ifence),
        .a_wbe(update_way | {CONFIG.ICACHE.WAYS{ifence}}),
        .a_wdata({CONFIG.ICACHE.WAYS{~ifence, stage2_tag}}),
        .a_addr(ifence ? ifence_addr : stage2_line_addr),
        .b_en(stage1_adv),
        .b_addr(stage1_line_addr),
        .b_rdata(tag_line),
    .*);

    always_comb begin
        for (int i = 0; i < CONFIG.ICACHE.WAYS; i++)
            tag_hit_way[i] = ({hit_allowed, 1'b1, stage2_tag} == {1'b1, tag_line[i]});
    end

    assign tag_hit = |tag_hit_way;

endmodule
