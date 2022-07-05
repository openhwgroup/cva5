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

module dcache_tag_banks 

    import cva5_config::*;
    import cva5_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG,
        parameter derived_cache_config_t SCONFIG = '{LINE_ADDR_W : 9, SUB_LINE_ADDR_W : 2, TAG_W : 15}
    )

    (
        input logic clk,
        input logic rst,

        //Port A
        input logic[31:0] load_addr,
        input logic load_req,
        input logic[31:0] miss_addr,
        input logic miss_req,
        input logic[CONFIG.DCACHE.WAYS-1:0] miss_way,
        input logic[31:0] inv_addr,
        input logic extern_inv,
        output logic extern_inv_complete,

        //Port B
        input logic[31:0] store_addr,
        input logic[31:0] store_addr_r,
        input logic store_req,

        output logic load_tag_hit,
        output logic store_tag_hit,
        output logic[CONFIG.DCACHE.WAYS-1:0] load_tag_hit_way,
        output logic[CONFIG.DCACHE.WAYS-1:0] store_tag_hit_way
    );

    typedef struct packed {
        logic valid;
        logic [SCONFIG.TAG_W-1:0] tag;
    } dtag_entry_t;

    cache_functions_interface # (.TAG_W(SCONFIG.TAG_W), .LINE_W(SCONFIG.LINE_ADDR_W), .SUB_LINE_W(SCONFIG.SUB_LINE_ADDR_W)) addr_utils ();

    dtag_entry_t  tag_line_a [CONFIG.DCACHE.WAYS-1:0];
    dtag_entry_t  tag_line_b [CONFIG.DCACHE.WAYS-1:0];

    dtag_entry_t new_tagline;

    logic [SCONFIG.LINE_ADDR_W-1:0] porta_addr;
    logic [SCONFIG.LINE_ADDR_W-1:0] portb_addr;

    logic external_inv;
    logic load_req_r;
    logic store_req_r;
    ////////////////////////////////////////////////////
    //Implementation
    always_ff @ (posedge clk) load_req_r <= load_req;
    always_ff @ (posedge clk) store_req_r <= store_req;

    assign external_inv = extern_inv & CONFIG.DCACHE.USE_EXTERNAL_INVALIDATIONS;

    assign porta_addr = miss_req ? addr_utils.getTagLineAddr(miss_addr) : external_inv ? addr_utils.getTagLineAddr(inv_addr) : addr_utils.getTagLineAddr(store_addr);
    assign portb_addr = addr_utils.getTagLineAddr(load_addr);

    assign extern_inv_complete = external_inv & ~miss_req;

    assign new_tagline = '{valid: miss_req, tag: addr_utils.getTag(miss_addr)};

    ////////////////////////////////////////////////////
    //Memory instantiation and hit detection
    generate for (genvar i = 0; i < CONFIG.DCACHE.WAYS; i++) begin : tag_bank_gen
        tag_bank #($bits(dtag_entry_t), CONFIG.DCACHE.LINES) dtag_bank ( 
            .clk (clk),
            .rst (rst),
            .en_a (store_req | (miss_req & miss_way[i]) | external_inv),
            .wen_a ((miss_req & miss_way[i]) | external_inv),
            .addr_a (porta_addr),
            .data_in_a (new_tagline),
            .data_out_a (tag_line_a[i]),
            .en_b (load_req),
            .wen_b ('0),
            .addr_b (portb_addr),
            .data_in_b ('0),
            .data_out_b(tag_line_b[i])
        );
        assign store_tag_hit_way[i] = ({store_req_r, 1'b1, addr_utils.getTag(store_addr_r)} == {1'b1, tag_line_a[i]});
        assign load_tag_hit_way[i] = ({load_req_r, 1'b1, addr_utils.getTag(miss_addr)} == {1'b1, tag_line_b[i]});
    end endgenerate

    assign load_tag_hit = |load_tag_hit_way;
    assign store_tag_hit = |store_tag_hit_way;

endmodule
