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

module fetch(
        input logic clk,
        input logic rst,
        input logic dec_advance,

        input logic exception,

        branch_table_interface.fetch bt,
        ras_interface.fetch ras,

        tlb_interface.mem tlb,
        bram_interface.user instruction_bram,
        input logic icache_on,
        l1_arbiter_request_interface.requester l1_request,
        l1_arbiter_return_interface.requester l1_response,

        instruction_buffer_interface.fetch ib,

        output logic[31:0] if2_pc,
        output logic flush

        );

    localparam BRAM_ID = 0;
    localparam ICACHE_ID = 1;

    fetch_sub_unit_interface fetch_sub[1:0]();

    logic cache_access;
    logic bram_access;

    logic mem_ready;

    logic [31:0] offset;
    logic [31:0] next_pc_source;
    logic [31:0] next_pc;

    logic [31:0] if_pc;
    logic stage1_prediction;

    logic new_mem_request;

    logic fetch_flush;
    logic new_issue;
    logic mem_valid;

    logic delayed_flush;

    logic [31:0] stage2_phys_address;
    logic stage2_valid;
    logic stage2_prediction;
    logic stage2_cache_access;

    logic pc_valid;

    logic[6:0] opcode;
    logic[2:0] fn3;

    logic csr_imm_op;
    logic sys_op;
    logic jal_jalr_x0;

    assign flush = bt.flush | exception;

    always_ff @(posedge clk) begin
        if (rst) begin
            pc_valid <= 0;
        end else begin
            pc_valid <= 1;
        end
    end

    assign bt.next_pc_valid = pc_valid;

    //Fetch PC
    always_ff @(posedge clk) begin
        if (rst) begin
            if_pc <= RESET_VEC;
            stage1_prediction <= 0;
        end
        else if (new_mem_request | flush) begin
            if_pc <= {next_pc[31:2], 2'b0};
            stage1_prediction <= bt.use_prediction & bt.prediction;
        end
    end


    always_comb begin
        if (exception)
            next_pc = RESET_VEC;
        else if (bt.flush)
            next_pc = bt.branch_taken ? bt.jump_pc : bt.njump_pc;
        else if (bt.use_prediction) begin
            if (bt.use_ras & ras.valid)
                next_pc = ras.addr;
            else
                next_pc = bt.predicted_pc;
        end
        else
            next_pc = if_pc + 4;
    end

    assign bt.new_mem_request = new_mem_request | bt.flush;
    assign bt.next_pc = next_pc;

    assign if2_pc  = if_pc;

    assign bt.if_pc = if_pc;
    /*************************************
     * TLB
     *************************************/
    assign tlb.virtual_address = if_pc;
    assign tlb.execute = 1;
    assign tlb.rnw = 0;

    always_ff @(posedge clk) begin
        if(rst)
            stage2_valid <= 0;
        if (new_mem_request)
            stage2_valid <= new_mem_request;
        else if (new_issue)
            stage2_valid <= 0;
    end

    always_ff @(posedge clk) begin
        if (new_mem_request) begin
            stage2_phys_address <= tlb.physical_address;
            stage2_prediction <= stage1_prediction;//not taken if no valid prediction
            stage2_cache_access <= cache_access;
        end
    end
    //////////////////////////////////////////////


    //Cache check done before cache access
    assign cache_access = tlb.physical_address[31:32-MEMORY_BIT_CHECK] == MEMORY_ADDR_L[31:32-MEMORY_BIT_CHECK];

    //BRAM check can be done a cycle later, can be used for address checking
    assign bram_access = stage2_phys_address[31:32-SCRATCH_BIT_CHECK] == SCRATCH_ADDR_L[31:32-SCRATCH_BIT_CHECK];

    assign mem_ready = fetch_sub[ICACHE_ID].ready;

    assign fetch_flush = (bt.flush | exception);
    assign new_mem_request =  pc_valid & tlb.complete & ~fetch_flush & ((stage2_valid & ~ib.early_full) |  (~stage2_valid & ~ib.full)) & mem_ready;


    assign fetch_sub[BRAM_ID].new_request = new_mem_request;
    assign fetch_sub[ICACHE_ID].new_request = new_mem_request & cache_access;

    assign fetch_sub[BRAM_ID].stage1_addr = tlb.physical_address;
    assign fetch_sub[ICACHE_ID].stage1_addr = tlb.physical_address;

    assign fetch_sub[BRAM_ID].stage2_addr = stage2_phys_address;
    assign fetch_sub[ICACHE_ID].stage2_addr = stage2_phys_address;

    //Memory interfaces
    generate if (USE_I_SCRATCH_MEM)
            ibram i_bram (.*, .fetch_sub(fetch_sub[BRAM_ID]));
        else
            assign  fetch_sub[BRAM_ID].ready = 1;
    endgenerate
    generate if (USE_ICACHE)
            icache i_cache (.*, .fetch_sub(fetch_sub[ICACHE_ID]));
        else
            assign  fetch_sub[ICACHE_ID].ready = 1;
    endgenerate
    //TODO potentially move support into cache so that we're not stalled on a request we no longer need due to a flush
    //If the cache is processing a miss when a flush occurs we need to discard the result once complete
    always_ff @(posedge clk) begin
        if (rst)
            delayed_flush <= 0;
        else if ((bt.flush | exception) & stage2_cache_access & ~fetch_sub[ICACHE_ID].data_valid)//& ~fetch_sub[ICACHE_ID].ready
            delayed_flush <= 1;
        else if (fetch_sub[ICACHE_ID].data_valid)
            delayed_flush <= 0;
    end

    assign mem_valid = ~(bt.flush | exception | delayed_flush);
    assign new_issue =  mem_valid & ((fetch_sub[BRAM_ID].data_valid & ~stage2_cache_access) | fetch_sub[ICACHE_ID].data_valid);
    assign ib.push = new_issue;
    assign ib.flush = bt.flush;

    assign ib.data_in.instruction =
        ({32{~stage2_cache_access}} & fetch_sub[BRAM_ID].data_out) |
        ({32{stage2_cache_access}} & fetch_sub[ICACHE_ID].data_out);

    assign ib.data_in.pc = stage2_phys_address;
    assign ib.data_in.prediction = stage2_prediction;


    //Early decode
    assign fn3 =ib.data_in.instruction[14:12];
    assign opcode = ib.data_in.instruction[6:0];

    assign csr_imm_op = (opcode == SYSTEM) && fn3[2];
    assign sys_op =  (opcode == SYSTEM) && (fn3 == 0);

    assign jal_jalr_x0 = ((opcode == JAL) || (opcode == JALR)) && (ib.data_in.instruction[11:7] == 0);

    assign ib.data_in.uses_rs1 = !((opcode == LUI) || (opcode == AUIPC) || (opcode == JAL) || (opcode == FENCE) || csr_imm_op || sys_op);
    assign ib.data_in.uses_rs2 = ((opcode == BRANCH) || (opcode == STORE) || (opcode == ARITH) || (opcode == AMO));
    assign ib.data_in.uses_rd = !((opcode == BRANCH) || (opcode == STORE) ||  (opcode == FENCE) || sys_op || jal_jalr_x0);


endmodule
