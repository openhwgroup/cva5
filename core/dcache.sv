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

module dcache(
        input logic clk,
        input logic rst,
        input logic dcache_on,
        l1_arbiter_request_interface.requester l1_request,
        l1_arbiter_return_interface.requester l1_response,
        input sc_complete,
        input sc_success,
        input clear_reservation,

        input data_access_shared_inputs_t ls_inputs,
        output logic[31:0] data_out,
        input logic lr,
        input logic sc,
        input logic is_amo,
        input logic [4:0] amo_op,

        input logic use_forwarded_data,
        output logic dcache_forward_data,
        output logic [2:0] dcache_stage2_fn3,

        ls_sub_unit_interface.sub_unit ls
        );

    logic tag_hit;
    logic [DCACHE_WAYS-1:0] tag_hit_way;

    logic [$clog2(DCACHE_WAYS)-1:0] tag_hit_way_int;

    logic tag_update;
    logic [DCACHE_WAYS-1:0] tag_update_way;
    logic [DCACHE_WAYS-1:0] replacement_way;

    logic [$clog2(DCACHE_WAYS)-1:0] replacement_way_int;
    logic [$clog2(DCACHE_WAYS)-1:0] tag_update_way_int;

    logic [DCACHE_SUB_LINE_ADDR_W-1:0] word_count;
    logic [DCACHE_SUB_LINE_ADDR_W-1:0] sc_write_index;
    logic [DCACHE_SUB_LINE_ADDR_W-1:0] update_word_index;

    logic line_complete;
    logic reservation;

    logic [31:0] stage2_addr;
    logic stage2_load;
    logic stage2_store;
    logic [3:0] stage2_be;
    logic [2:0] stage2_fn3;
    logic [31:0] stage2_data_in;
    logic [31:0] stage2_data;

    logic stage2_use_forwarded_data;
    logic [31:0] stage2_forwarded_data;

    logic stage2_lr;
    logic stage2_sc;
    logic stage2_is_amo;
    logic [4:0] stage2_amo_op;


    logic [31:0] dbank_data_out;
    logic [31:0] hit_data;
    logic [31:0] miss_data;
    logic [31:0] new_line_data;
    logic [31:0] amo_result;
    logic [31:0] amo_rs2;

    logic[3:0] write_hit_be;

    logic second_cycle;

    logic request;

    logic is_target_word;

    logic hit_allowed;
    logic read_hit_allowed;
    logic read_hit_data_valid;

    logic address_range_valid;

    logic idle;
    logic read_miss_complete;

    logic store_complete;
    amo_alu_inputs_t amo_alu_inputs;

    const bit[DCACHE_SUB_LINE_ADDR_W-1:0] SUBLINE_PADDING= '0;

    /*************************************
     * 2nd cycle signals
     *************************************/
    always_ff @ (posedge clk) begin
        if(rst)
            stage2_use_forwarded_data <= 0;
        else if (ls.new_request)
            stage2_use_forwarded_data <= use_forwarded_data;
        else if (store_complete)
            stage2_use_forwarded_data <= 0;
    end

    always_ff @ (posedge clk) begin
        if (ls.new_request) begin
            stage2_addr <= ls_inputs.addr;
            stage2_be <= ls_inputs.be;
            stage2_load <= ls_inputs.load;
            stage2_store <= ls_inputs.store;
            stage2_fn3 <= ls_inputs.fn3;
            stage2_data_in <= ls_inputs.data_in;
            if (USE_AMO) begin
                stage2_lr <= lr;
                stage2_is_amo <= is_amo; //excludes lr/sc
                stage2_sc <= sc;
                stage2_amo_op <= amo_op;
            end else begin
                stage2_lr <= 0;
                stage2_is_amo <= 0; //excludes lr/sc
                stage2_sc <= 0;
                stage2_amo_op <= 0;
            end
        end
    end

    assign dcache_stage2_fn3 = stage2_fn3;
    assign dcache_forward_data = stage2_use_forwarded_data;

    /*************************************
     * General Control Logic
     *************************************/
    //LR and AMO ops are forced misses (if there is a tag hit they will reuse the same way however)
    //Signal is valid only for a single cycle, RAM enables are used to hold outputs in case of pipeline stalls
    always_ff @ (posedge clk) begin
        if (rst)
            read_hit_allowed <= 0;
        else
            read_hit_allowed <= ls.new_request & ls_inputs.load & dcache_on & ~(lr | is_amo);
    end

    always_ff @ (posedge clk) begin
        if (rst)
            read_hit_data_valid <= 0;
        else
            read_hit_data_valid <= read_hit_allowed;
    end


    //LR reservation, cleared on exceptions
    always_ff @ (posedge clk) begin
        if (rst)
            reservation <= 0;
        else if (second_cycle)
            reservation <= stage2_lr;
        else if (sc_complete | clear_reservation)
            reservation <= 0;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            second_cycle <= 0;
        else
            second_cycle <= ls.new_request;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            tag_update <= 0;
        else if (second_cycle)
            tag_update <= dcache_on & stage2_load & ~tag_hit;        //Cache enabled, read miss
        else
            tag_update <= 0;
    end

    /*************************************
     * L1 Arbiter Interface
     *************************************/
    assign l1_request.addr = {stage2_addr[31:2], 2'b0} ;//Memory interface aligns request to burst size (done there to support AMO line-read word-write)
    assign l1_request.data = stage2_data;
    assign l1_request.rnw = stage2_load;
    assign l1_request.be = stage2_be;
    assign l1_request.size = stage2_load ? (DCACHE_LINE_W-1) : 0;//LR and AMO ops are included in load
    assign l1_request.is_amo = (stage2_is_amo | stage2_lr | stage2_sc);
    assign l1_request.amo = stage2_amo_op;

    always_ff @ (posedge clk) begin
        if (rst)
            word_count <= 0;
        else if (l1_response.data_valid)
            word_count <= word_count + 1;
    end
    assign is_target_word = (stage2_addr[DCACHE_SUB_LINE_ADDR_W+1:2] == word_count);

    always_ff @ (posedge clk) begin
        if (rst)
            request  <= 0;
        else if (second_cycle & ~l1_request.ack)
            request <= ~(tag_hit & read_hit_allowed) | ~dcache_on;
        else if (l1_request.ack)
            request <= 0;
    end
    assign l1_request.request = request | (second_cycle & (~(tag_hit & read_hit_allowed) | ~dcache_on));

    /*************************************
     * Cache Components
     *************************************/
    //Free running one hot cycler.
    cycler #(DCACHE_WAYS) replacement_policy (.*, .en(1'b1), .one_hot(replacement_way));

    //One-hot tag hit / update logic to binary int
    one_hot_to_integer #(DCACHE_WAYS) hit_way_conv (.one_hot(tag_hit_way), .int_out(tag_hit_way_int));
    one_hot_to_integer #(DCACHE_WAYS) update_way_conv (.one_hot(replacement_way), .int_out(replacement_way_int));


    //If atomic load (LR or AMO op) and there's a tag hit reuse same line
    always_ff @ (posedge clk) begin
        if (second_cycle) begin
            tag_update_way<= ((stage2_is_amo | stage2_lr) & tag_hit) ? tag_hit_way : replacement_way;
            tag_update_way_int <= ((stage2_is_amo | stage2_lr) & tag_hit) ? tag_hit_way_int : replacement_way_int;
        end
    end


    //Tag banks
    dtag_banks dcache_tag_banks (.*,
            .stage1_addr(ls_inputs.addr),
            .stage2_addr(stage2_addr),
            .inv_addr({l1_response.inv_addr, 2'b00}),
            .update_way(tag_update_way),
            .update(tag_update),
            .stage1_adv(ls.new_request),
            .stage1_inv(1'b0),//For software invalidation
            .extern_inv(l1_response.inv_valid),
            .extern_inv_complete(l1_response.inv_ack)
        );


    assign write_hit_be = stage2_be & {4{tag_hit}};

    //AMO op processing on incoming data
    always_ff @ (posedge clk) begin
        amo_rs2 <= stage2_data_in; //Only forwarding on STORE opcode
    end

    assign amo_alu_inputs.rs1_load = l1_response.data;
    assign amo_alu_inputs.rs2 = amo_rs2;
    assign amo_alu_inputs.op = stage2_amo_op;

    generate if (USE_AMO)
            amo_alu amo_unit (.*, .result(amo_result));
    endgenerate

    always_comb begin
        if (stage2_is_amo & is_target_word)
            new_line_data = amo_result;
        else if (stage2_sc)
            new_line_data = stage2_data_in;//Only forwarding on STORE opcode
        else
            new_line_data = l1_response.data;
    end


    assign sc_write_index = stage2_addr[DCACHE_SUB_LINE_ADDR_W+1:2];
    assign update_word_index = stage2_sc ? sc_write_index : word_count;
    ////////////////////////////////////////////////////////
    assign stage2_data = stage2_use_forwarded_data ? ls_inputs.data_in : stage2_data_in;

    //Data Bank(s)
    ddata_bank #(DCACHE_LINES*DCACHE_LINE_W*DCACHE_WAYS) data_bank (
            .clk(clk),
            .addr_a({tag_hit_way_int, stage2_addr[DCACHE_LINE_ADDR_W+DCACHE_SUB_LINE_ADDR_W+2-1:2]}),
            .addr_b({tag_update_way_int, stage2_addr[DCACHE_LINE_ADDR_W+DCACHE_SUB_LINE_ADDR_W+2-1:DCACHE_SUB_LINE_ADDR_W+2], update_word_index}),
            .en_a(second_cycle),
            .en_b(l1_response.data_valid | (sc_complete & sc_success)),
            .be_a(write_hit_be),
            .data_in_a(stage2_data),
            .data_in_b(new_line_data),
            .data_out_a(dbank_data_out)
        );


    /*************************************
     * Output Muxing
     *************************************/
    always_ff @ (posedge clk) begin
        if (l1_response.data_valid & is_target_word)
            miss_data <= l1_response.data;
        else if (sc_complete)
            miss_data <= {31'b0, sc_success};
        else
            miss_data <= 0;
    end

    assign data_out = miss_data | ({32{read_hit_data_valid}} & dbank_data_out);

    /*************************************
     * Pipeline Advancement
     *************************************/
    assign line_complete = (l1_response.data_valid && (word_count == (DCACHE_LINE_W-1))); //covers load, LR, AMO
    assign store_complete = l1_request.ack & stage2_store & ~stage2_sc;

    always_ff @ (posedge clk) begin
        if (rst)
            ls.data_valid <= 0;
        else
            ls.data_valid <= ((l1_response.data_valid & is_target_word) | (read_hit_allowed & tag_hit) | sc_complete);
    end

    //read miss complete includes store conditional complete
    always_ff @ (posedge clk) begin
        if (rst)
            read_miss_complete <= 0;
        else
            read_miss_complete <= line_complete | sc_complete;
    end

    assign ls.ready = (read_hit_allowed & tag_hit) | store_complete | (read_miss_complete) | idle;

    always_ff @ (posedge clk) begin
        if (rst)
            idle <= 1;
        else if (ls.new_request)
            idle <= 0;
        else if ((read_hit_allowed & tag_hit) | read_miss_complete | store_complete) //read miss OR write through complete
            idle <= 1;
    end



endmodule
