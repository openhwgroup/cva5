/*
 * Copyright © 2017, 2018 Eric Matthews,  Lesley Shannon
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

        input logic gc_fetch_flush,
        input logic gc_fetch_pc_override,
        input logic exception,
        input logic [31:0] gc_fetch_pc,

        branch_table_interface.fetch bt,
        ras_interface.fetch ras,

        tlb_interface.mem tlb,
        local_memory_interface.master instruction_bram,
        input logic icache_on,
        l1_arbiter_request_interface.requester l1_request,
        l1_arbiter_return_interface.requester l1_response,

        instruction_buffer_interface.fetch ib,

        output logic[31:0] if2_pc

        );

    localparam NUM_SUB_UNITS = USE_I_SCRATCH_MEM + USE_ICACHE;
    localparam NUM_SUB_UNITS_W = $clog2(NUM_SUB_UNITS);

    localparam BRAM_ID = 0;
    localparam ICACHE_ID = USE_I_SCRATCH_MEM;

    fetch_sub_unit_interface fetch_sub[NUM_SUB_UNITS-1:0]();

    logic [NUM_SUB_UNITS-1:0] sub_unit_address_match;
    logic [NUM_SUB_UNITS-1:0] last_sub_unit_id;
    logic [NUM_SUB_UNITS-1:0] unit_ready;
    logic [NUM_SUB_UNITS-1:0] unit_data_valid;
    logic [31:0] unit_data_array [NUM_SUB_UNITS-1:0];
    logic [31:0] anded_unit_data_array [NUM_SUB_UNITS-1:0];

    logic units_ready;


    logic [31:0] next_pc;
    logic [31:0] if_pc;

    logic space_in_inst_buffer;
    logic mem_ready;
    logic new_mem_request;

    logic new_issue;
    logic mem_valid;

    logic delayed_flush;

    logic [31:0] stage2_phys_address;
    logic stage2_valid;

    logic update_pc;

    logic [31:0] final_instruction;
    logic [6:0] opcode;
    logic [4:0] opcode_trimmed;
    logic [4:0] rs1_addr;
    logic [4:0] rs2_addr;
    logic [4:0] rd_addr;
    logic [2:0] fn3;

    logic csr_imm_op;
    logic sys_op;
    logic jal_jalr_x0;

    logic rs1_link, rd_link, rs1_eq_rd, use_ras;
    logic[$clog2(FETCH_BUFFER_DEPTH+1)-1:0] inflight_count;
    /////////////////////////////////////////

    genvar i;
    generate
        for(i=0; i < NUM_SUB_UNITS; i++) begin
            assign unit_ready[i] = fetch_sub[i].ready;
            assign unit_data_valid[i] = fetch_sub[i].data_valid;
        end
    endgenerate
    assign units_ready = &unit_ready;

    assign update_pc = mem_ready | gc_fetch_flush;

    //Fetch PC
    always_ff @(posedge clk) begin
        if (rst)
            if_pc <= RESET_VEC;
        else if (update_pc)
            if_pc <= {next_pc[31:2], 2'b0};
    end

    always_comb begin
        if (gc_fetch_pc_override)
            next_pc = gc_fetch_pc;
        else if (gc_fetch_flush)
            next_pc = bt.branch_taken ? bt.jump_pc : bt.njump_pc;
        else if (bt.use_prediction)
            next_pc = (bt.use_ras & ras.valid) ? ras.addr : bt.predicted_pc;
        else
            next_pc = if_pc + 4;
    end

    assign bt.new_mem_request = update_pc;
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
        if (new_mem_request) begin
            stage2_phys_address <= tlb.physical_address;
        end
    end
    //////////////////////////////////////////////

    always_ff @(posedge clk) begin
        if (rst | gc_fetch_flush)
            inflight_count <= 0;
        else if (mem_ready  & ~ib.pop)
            inflight_count <= inflight_count + 1;
        else if (~mem_ready &  ib.pop)
            inflight_count <= inflight_count - 1;
    end

    always_ff @(posedge clk) begin
        if (rst | gc_fetch_flush)
            space_in_inst_buffer <= 1;
        else if (mem_ready  & ~ib.pop)
            space_in_inst_buffer <= inflight_count < (FETCH_BUFFER_DEPTH-1);
        else if (~mem_ready &  ib.pop)
            space_in_inst_buffer <= 1;
    end

//assign space_in_inst_buffer = inflight_count < FETCH_BUFFER_DEPTH;
    assign mem_ready = tlb.complete & space_in_inst_buffer & units_ready;
    assign new_mem_request = mem_ready & (~gc_fetch_flush);

    //Memory interfaces
    generate if (USE_I_SCRATCH_MEM) begin
            ibram i_bram (.*, .fetch_sub(fetch_sub[BRAM_ID]));
            assign sub_unit_address_match[BRAM_ID] = (tlb.physical_address[31:32-SCRATCH_BIT_CHECK] == SCRATCH_ADDR_L[31:32-SCRATCH_BIT_CHECK]);
            assign fetch_sub[BRAM_ID].new_request = new_mem_request & sub_unit_address_match[BRAM_ID];
            assign fetch_sub[BRAM_ID].stage1_addr = tlb.physical_address;
            assign fetch_sub[BRAM_ID].stage2_addr = stage2_phys_address;
            assign unit_data_array[BRAM_ID] = fetch_sub[BRAM_ID].data_out;
        end
    endgenerate
    generate if (USE_ICACHE) begin
            icache i_cache (.*, .fetch_sub(fetch_sub[ICACHE_ID]));
            assign sub_unit_address_match[ICACHE_ID] = tlb.physical_address[31:32-MEMORY_BIT_CHECK] == MEMORY_ADDR_L[31:32-MEMORY_BIT_CHECK];
            assign fetch_sub[ICACHE_ID].new_request = new_mem_request & sub_unit_address_match[ICACHE_ID];
            assign fetch_sub[ICACHE_ID].stage1_addr = tlb.physical_address;
            assign fetch_sub[ICACHE_ID].stage2_addr = stage2_phys_address;
            assign unit_data_array[ICACHE_ID] = fetch_sub[ICACHE_ID].data_out;

            always_ff @(posedge clk) begin
                if(rst | gc_fetch_flush)
                    stage2_valid <= 0;
                else if (mem_ready)
                    stage2_valid <= 1;
                else if (new_issue)
                    stage2_valid <= 0;
            end

            always_ff @(posedge clk) begin
                if (new_mem_request) begin
                    last_sub_unit_id <= sub_unit_address_match;
                end
            end
            //TODO potentially move support into cache so that we're not stalled on a request we no longer need due to a flush
            //If the cache is processing a miss when a flush occurs we need to discard the result once complete
            always_ff @(posedge clk) begin
                if (rst)
                    delayed_flush <= 0;
                else if (gc_fetch_flush & stage2_valid & last_sub_unit_id[ICACHE_ID] & ~fetch_sub[ICACHE_ID].data_valid)//& ~fetch_sub[ICACHE_ID].ready
                    delayed_flush <= 1;
                else if (fetch_sub[ICACHE_ID].data_valid)
                    delayed_flush <= 0;
            end
        end else begin
            assign delayed_flush = 0;
        end
    endgenerate

    assign mem_valid = ~(gc_fetch_flush | delayed_flush);
    assign new_issue =  mem_valid & (|unit_data_valid);
    assign ib.push = new_issue;
    assign ib.flush = gc_fetch_flush;


    //bitwise AND all subunit outputs with valid signal then or all outputs together
    always_comb begin
        final_instruction = 0;
        foreach (unit_data_array[i]) begin
            anded_unit_data_array[i] = unit_data_array[i] & {$bits(unit_data_array[i]){unit_data_valid[i]}};
            final_instruction |= anded_unit_data_array[i];
        end
    end

    assign ib.data_in.instruction = final_instruction;
    assign ib.data_in.pc = stage2_phys_address;

    ///////////////////////////////////
    //Early decode
    ///////////////////////////////////
    assign fn3 = final_instruction[14:12];
    assign opcode = final_instruction[6:0];
    assign opcode_trimmed = opcode[6:2];

    assign rs1_addr = final_instruction[19:15];
    assign rs2_addr = final_instruction[24:20];
    assign rd_addr  = final_instruction[11:7];

    assign csr_imm_op = (opcode_trimmed == SYSTEM_T) && fn3[2];
    assign sys_op =  (opcode_trimmed == SYSTEM_T) && (fn3 == 0);

    assign jal_jalr_x0 = (opcode_trimmed inside {JAL_T, JALR_T}) && (rd_addr == 0);

    //RAS support ///////////////////
    assign rs1_link = (rs1_addr inside {1,5});
    assign rd_link = (rd_addr inside {1,5});
    assign rs1_eq_rd = (rs1_addr == rd_addr);
    assign use_ras =  (opcode_trimmed == JALR_T) && ((rs1_link & ~rd_link) | (rs1_link & rd_link & ~rs1_eq_rd));
    ///////////////////////////////////

    //Output FIFO
    assign ib.data_in.uses_rs1 = !(opcode_trimmed inside {LUI_T, AUIPC_T, JAL_T, FENCE_T} || csr_imm_op || sys_op);
    assign ib.data_in.uses_rs2 = opcode_trimmed inside {BRANCH_T, STORE_T, ARITH_T, AMO_T};
    assign ib.data_in.uses_rd = !(opcode_trimmed inside {BRANCH_T, STORE_T, FENCE_T} || sys_op || jal_jalr_x0);
    assign ib.data_in.rd_zero = (rd_addr == 0);

    assign ib.data_in.is_return = use_ras;
    assign ib.data_in.is_call = (opcode_trimmed inside {JAL_T, JALR_T}) && rd_link;

endmodule
