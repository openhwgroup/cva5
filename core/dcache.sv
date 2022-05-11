/*
 * Copyright © 2017-2020 Eric Matthews,  Lesley Shannon
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
        input logic uncacheable,
        memory_sub_unit_interface.responder ls
    );

    localparam DCACHE_SIZE_IN_WORDS = CONFIG.DCACHE.LINES*CONFIG.DCACHE.LINE_W*CONFIG.DCACHE.WAYS;
    localparam derived_cache_config_t SCONFIG = get_derived_cache_params(CONFIG, CONFIG.DCACHE, CONFIG.DCACHE_ADDR);

    typedef struct packed{
        logic [29:0] addr;
        logic [3:0] be;
        logic load;
        logic store;
        logic [31:0] data;
        amo_details_t amo;
        logic uncacheable;
    } stage2_t;

    logic [$clog2(DCACHE_SIZE_IN_WORDS)-1:0] data_bank_addr_a;
    logic [$clog2(DCACHE_SIZE_IN_WORDS)-1:0] data_bank_addr_b;

    logic tag_hit;
    logic [CONFIG.DCACHE.WAYS-1:0] tag_hit_way;

    logic [$clog2(CONFIG.DCACHE.WAYS)-1:0] tag_hit_way_int;

    logic tag_update;
    logic [CONFIG.DCACHE.WAYS-1:0] tag_update_way;
    logic [CONFIG.DCACHE.WAYS-1:0] replacement_way;

    logic [$clog2(CONFIG.DCACHE.WAYS)-1:0] replacement_way_int;
    logic [$clog2(CONFIG.DCACHE.WAYS)-1:0] tag_update_way_int;

    logic [SCONFIG.SUB_LINE_ADDR_W-1:0] word_count;
    logic [SCONFIG.SUB_LINE_ADDR_W-1:0] sc_write_index;
    logic [SCONFIG.SUB_LINE_ADDR_W-1:0] update_word_index;

    logic line_complete;
    logic reservation;

    stage2_t stage2;

    logic [31:0] dbank_data_out;
    logic [31:0] hit_data;
    logic [31:0] miss_data;
    logic [31:0] new_line_data;
    logic [31:0] amo_result;
    logic [31:0] amo_rs2;

    logic[3:0] write_hit_be;

    logic second_cycle;

    logic new_arb_request;
    logic arb_request_r;

    logic is_target_word;

    logic hit_allowed;
    logic read_hit_allowed;
    logic read_hit_data_valid;
    logic read_hit;

    logic address_range_valid;

    logic idle;
    logic read_miss_complete;

    logic store_complete;
    amo_alu_inputs_t amo_alu_inputs;



    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //2nd Cycle Control Signals
    always_ff @ (posedge clk) begin
        if (ls.new_request) begin
            stage2.addr <= ls.addr[31:2];
            stage2.be <= ls.be;
            stage2.load <= ls.re;
            stage2.store <= ls.we;
            stage2.data <= ls.data_in;
            stage2.amo <= amo;
            stage2.uncacheable <= uncacheable;
        end
    end

    ////////////////////////////////////////////////////
    //General Control Logic
    //LR and AMO ops are forced misses (if there is a tag hit they will reuse the same way)
    //Signal is valid for a single cycle, RAM enables are used to hold outputs in case of pipeline stalls
    always_ff @ (posedge clk) begin
        read_hit_allowed <= ls.new_request & ls.re & dcache_on & ~(amo.is_lr | amo.is_amo) & ~uncacheable;
        read_hit_data_valid <= read_hit_allowed;
        second_cycle <= ls.new_request;
        tag_update <= second_cycle & dcache_on & stage2.load & ~tag_hit & ~stage2.uncacheable;//Cache enabled, read miss
    end

    assign read_hit = tag_hit & read_hit_allowed;

    //LR reservation, cleared on exceptions

    always_ff @ (posedge clk) begin
        if (rst)
            reservation <= 0;
        else if (second_cycle)
            reservation <= stage2.amo.is_lr;
        else if (sc_complete | clear_reservation)
            reservation <= 0;
    end

    ////////////////////////////////////////////////////
    //L1 Arbiter Interface
    assign l1_request.addr = {stage2.addr, 2'b0} ;//Memory interface aligns request to burst size (done there to support AMO line-read word-write)
    assign l1_request.data = stage2.data;
    assign l1_request.rnw = ~stage2.store;
    assign l1_request.be = stage2.be;
    assign l1_request.size = (stage2.load & ~stage2.uncacheable) ? 5'(CONFIG.DCACHE.LINE_W-1) : 0;//LR and AMO ops are included in load
    assign l1_request.is_amo = (stage2.amo.is_amo | stage2.amo.is_lr | stage2.amo.is_sc);
    assign l1_request.amo = stage2.amo.op;

    always_ff @ (posedge clk) begin
        if (rst | line_complete)
            word_count <= 0;
        else if (l1_response.data_valid)
            word_count <= word_count + 1;
    end
    assign is_target_word = (stage2.addr[SCONFIG.SUB_LINE_ADDR_W-1:0] == word_count) | stage2.uncacheable;

    assign new_arb_request = second_cycle & (~read_hit);
    always_ff @ (posedge clk) begin
        if (rst)
            arb_request_r  <= 0;
        else if (second_cycle & ~l1_request.ack)
            arb_request_r <= new_arb_request;
        else if (l1_request.ack)
            arb_request_r  <= 0;
    end
    assign l1_request.request = new_arb_request | arb_request_r;

    ////////////////////////////////////////////////////
    //Replacement policy (free runing one-hot cycler, i.e. pseudo random)
    cycler #(CONFIG.DCACHE.WAYS) replacement_policy (
        .clk        (clk),
        .rst        (rst),
        .en         (1'b1), 
        .one_hot    (replacement_way)
    );

    //One-hot tag hit / update logic to binary int
    one_hot_to_integer #(CONFIG.DCACHE.WAYS)
    hit_way_conv (
        .one_hot(tag_hit_way), 
        .int_out(tag_hit_way_int)
    );
    one_hot_to_integer #(CONFIG.DCACHE.WAYS)
    update_way_conv (
        .one_hot    (replacement_way), 
        .int_out    (replacement_way_int)
    );


    //If atomic load (LR or AMO op) and there's a tag hit reuse same line
    logic stage2_amo_with_load;
    assign stage2_amo_with_load = stage2.amo.is_amo | stage2.amo.is_lr;
    always_ff @ (posedge clk) begin
        if (second_cycle) begin
            tag_update_way<= (stage2_amo_with_load & tag_hit) ? tag_hit_way : replacement_way;
            tag_update_way_int <= (stage2_amo_with_load & tag_hit) ? tag_hit_way_int : replacement_way_int;
        end
    end

    ////////////////////////////////////////////////////
    //Tag banks
    dtag_banks #(.CONFIG(CONFIG), .SCONFIG(SCONFIG))
    dcache_tag_banks (
        .clk (clk),
        .rst (rst),
        .stage1_addr (ls.addr[31:2]),
        .stage2_addr (stage2.addr),
        .inv_addr (l1_response.inv_addr),
        .update_way (tag_update_way),
        .update (tag_update),
        .stage1_adv (ls.new_request),
        .stage1_inv (1'b0),//For software invalidation
        .extern_inv (l1_response.inv_valid),
        .extern_inv_complete (l1_response.inv_ack),
        .tag_hit (tag_hit),
        .tag_hit_way (tag_hit_way)
    );

    ////////////////////////////////////////////////////
    //AMO logic
    always_ff @ (posedge clk) begin
        amo_rs2 <= stage2.data;
    end

    assign amo_alu_inputs.rs1_load = l1_response.data;
    assign amo_alu_inputs.rs2 = amo_rs2;
    assign amo_alu_inputs.op = stage2.amo.op;

    generate if (CONFIG.INCLUDE_AMO)
        amo_alu amo_unit (
            .amo_alu_inputs (amo_alu_inputs), 
            .result (amo_result)
        );
    endgenerate

    always_comb begin
        if (stage2.amo.is_amo & is_target_word)
            new_line_data = amo_result;
        else if (stage2.amo.is_sc)
            new_line_data = stage2.data;
        else
            new_line_data = l1_response.data;
    end

    assign sc_write_index = stage2.addr[SCONFIG.SUB_LINE_ADDR_W-1:0];


    ////////////////////////////////////////////////////
    //Data Bank(s)
    //Tag bank selection done with upper address bits
    //On miss, word index in line provided by: update_word_index
    assign write_hit_be = stage2.be & {4{tag_hit}};
    assign update_word_index = stage2.amo.is_sc ? sc_write_index : word_count;

    generate if (CONFIG.DCACHE.WAYS == 1) begin : bank_sel_gen
        assign data_bank_addr_a = stage2.addr[SCONFIG.LINE_ADDR_W+SCONFIG.SUB_LINE_ADDR_W-1:0];
        assign data_bank_addr_b = {stage2.addr[SCONFIG.LINE_ADDR_W+SCONFIG.SUB_LINE_ADDR_W-1:SCONFIG.SUB_LINE_ADDR_W], update_word_index};
    end else begin
        assign data_bank_addr_a = {tag_hit_way_int, stage2.addr[SCONFIG.LINE_ADDR_W+SCONFIG.SUB_LINE_ADDR_W-1:0]};
        assign data_bank_addr_b = {tag_update_way_int, stage2.addr[SCONFIG.LINE_ADDR_W+SCONFIG.SUB_LINE_ADDR_W-1:SCONFIG.SUB_LINE_ADDR_W], update_word_index};
    end endgenerate

    ddata_bank #(.LINES(DCACHE_SIZE_IN_WORDS)) data_bank (
            .clk(clk),
            .addr_a(data_bank_addr_a),
            .addr_b(data_bank_addr_b),
            .en_a(second_cycle),
            .en_b((l1_response.data_valid & ~stage2.uncacheable) | (sc_complete & sc_success)),
            .be_a(write_hit_be),
            .data_in_a(stage2.data),
            .data_in_b(new_line_data),
            .data_out_a(dbank_data_out)
        );

    ////////////////////////////////////////////////////
    //Output
    always_ff @ (posedge clk) begin
        if (l1_response.data_valid & is_target_word)
            miss_data <= l1_response.data;
        else if (sc_complete)
            miss_data <= {31'b0, sc_success};
    end

    assign ls.data_out = read_hit_data_valid ? dbank_data_out : miss_data;

    ////////////////////////////////////////////////////
    //Pipeline Advancement
    assign line_complete = l1_response.data_valid & ((word_count == $clog2(CONFIG.DCACHE.LINE_W)'(CONFIG.DCACHE.LINE_W-1)) | stage2.uncacheable); //covers load, LR, AMO
    assign store_complete = l1_request.ack & stage2.store & ~stage2.amo.is_sc;

    //read miss complete includes store conditional complete
    always_ff @ (posedge clk) begin
        if (rst)
            read_miss_complete <= 0;
        else
            read_miss_complete <= line_complete | sc_complete;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            ls.data_valid <= 0;
        else
            ls.data_valid <= (l1_response.data_valid & is_target_word) | read_hit | sc_complete;
    end

    assign ls.ready = read_hit | store_complete | read_miss_complete | idle;

    always_ff @ (posedge clk) begin
        if (rst)
            idle <= 1;
        else if (ls.new_request)
            idle <= 0;
        else if (ls.ready)
            idle <= 1;
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    dcache_request_when_not_ready_assertion:
        assert property (@(posedge clk) disable iff (rst) ls.new_request |-> ls.ready)
        else $error("dcache received request when not ready");

endmodule
