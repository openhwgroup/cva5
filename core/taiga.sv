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

module taiga (
        input logic clk,
        input logic rst,

        local_memory_interface.master instruction_bram,
        local_memory_interface.master data_bram,

        axi_interface.master m_axi,
        avalon_interface.master m_avalon,

        l2_requester_interface.requester l2,

        output logic [31:0] dec_pc_debug,
        output logic dec_advance_debug,
        output logic [31:0] dec_instruction,
        output logic [31:0] if2_pc_debug,

        input logic timer_interrupt,
        input logic interrupt,

        output logic placer_rseed
        );

    l1_arbiter_request_interface l1_request[L1_CONNECTIONS-1:0]();
    l1_arbiter_return_interface l1_response[L1_CONNECTIONS-1:0]();
    logic sc_complete;
    logic sc_success;

    branch_table_interface bt();
    ras_interface ras();

    register_file_decode_interface rf_decode();
    alu_inputs_t alu_inputs;
    load_store_inputs_t ls_inputs;
    branch_inputs_t branch_inputs;
    mul_inputs_t mul_inputs;
    div_inputs_t div_inputs;
    gc_inputs_t gc_inputs;

    func_unit_ex_interface branch_ex();
    func_unit_ex_interface alu_ex();
    func_unit_ex_interface ls_ex();
    func_unit_ex_interface gc_ex();
    func_unit_ex_interface mul_ex();
    func_unit_ex_interface div_ex();

    instruction_buffer_interface ib();

    exception_packet_t  ls_exception;

    tracking_interface ti();
    unit_writeback_interface unit_wb [NUM_WB_UNITS-1:0]();
    register_file_writeback_interface rf_wb();

    mmu_interface immu();
    mmu_interface dmmu();

    tlb_interface itlb();
    tlb_interface dtlb();
    logic tlb_on;
    logic [ASIDLEN-1:0] asid;
    logic return_from_exception;

    //Global Control
    logic load_store_FIFO_emptying;
    logic gc_issue_hold;
    logic gc_fetch_flush;
    logic gc_fetch_pc_override;
    logic gc_supress_writeback;
    logic gc_flush_LS_input;
    logic inorder;
    logic inuse_clear;
    instruction_id_t oldest_id;
    logic inflight_queue_empty;
    logic load_store_issue;
    logic [31:0] gc_fetch_pc;

    logic store_committed;
    instruction_id_t store_id;


    //Branch Unit and Fetch Unit
    logic branch_taken;
    logic [31:0] pc_offset;
    logic[31:0] jalr_rs1;
    logic jalr;
    logic branch_miss_predict;

    //Decode Unit and Fetch Unit
    logic [31:0] if2_pc;
    logic dec_instruction_issued;
    logic illegal_instruction;

    logic [31:0] dec_pc;
    logic [31:0] pc_ex;

    logic instruction_queue_empty;

    logic instruction_issued_no_rd;
    logic instruction_issued_with_rd;
    logic instruction_complete;
    logic instruction_issued;

    assign if2_pc_debug = if2_pc;
    assign dec_pc_debug = dec_pc;
    assign dec_advance_debug = dec_instruction_issued;
    assign instruction_issued = dec_instruction_issued;

    placer_randomizer # (8'h2B)
        rseed_generator (.*, .result(placer_rseed),
            .samples({if2_pc[23], ib.data_in.instruction[9], rf_decode.rs1_data[1], rf_decode.rs2_conflict, ti.issue_id[1], ls_ex.new_request, unit_wb[DIV_UNIT_WB_ID].rd[7], unit_wb[ALU_UNIT_WB_ID].rd[28]})
            );


    /*************************************
     * Memory Interface
     *************************************/
    generate if (ENABLE_S_MODE || USE_ICACHE || USE_DCACHE)
            l1_arbiter arb(.*);
    endgenerate

    /*************************************
     * CPU Front end
     *************************************/
    fetch fetch_block (.*, .icache_on('1), .tlb(itlb), .l1_request(l1_request[L1_ICACHE_ID]), .l1_response(l1_response[L1_ICACHE_ID]), .exception(1'b0));
    branch_table bt_block (.*);
    assign branch_miss_predict = bt.flush;
    ras ras_block(.*);
    generate if (ENABLE_S_MODE) begin
            tlb_lut_ram #(ITLB_WAYS, ITLB_DEPTH) i_tlb (.*, .tlb(itlb), .mmu(immu));
            mmu i_mmu (.*,  .mmu(immu) , .l1_request(l1_request[L1_IMMU_ID]), .l1_response(l1_response[L1_IMMU_ID]), .mmu_exception());
        end
        else begin
            assign itlb.complete = 1;
            assign itlb.physical_address = itlb.virtual_address;
        end
    endgenerate
    instruction_buffer inst_buffer(.*);

    /*************************************
     * Decode/Issue
     *************************************/
    decode decode_block (.*);
    register_file register_file_block (.*);
    /*************************************
     * Units
     *************************************/

    branch_unit branch_unit_block (.*, .branch_wb(unit_wb[BRANCH_UNIT_WB_ID]));
    alu_unit alu_unit_block (.*, .alu_wb(unit_wb[ALU_UNIT_WB_ID]));
    load_store_unit load_store_unit_block (.*, .dcache_on(1'b1), .clear_reservation(1'b0), .tlb(dtlb), .ls_wb(unit_wb[LS_UNIT_WB_ID]), .l1_request(l1_request[L1_DCACHE_ID]), .l1_response(l1_response[L1_DCACHE_ID]));
    generate if (ENABLE_S_MODE) begin
            tlb_lut_ram #(DTLB_WAYS, DTLB_DEPTH) d_tlb (.*, .tlb(dtlb), .mmu(dmmu));
            mmu d_mmu (.*, .mmu(dmmu), .l1_request(l1_request[L1_DMMU_ID]), .l1_response(l1_response[L1_DMMU_ID]), .mmu_exception());
        end
        else begin
            assign dtlb.complete = 1;
            assign dtlb.physical_address = dtlb.virtual_address;
        end
    endgenerate
    gc_unit gc_unit_block (.*, .gc_wb(unit_wb[GC_UNIT_WB_ID]));

    generate if (USE_MUL)
            mul_unit mul_unit_block (.*, .mul_wb(unit_wb[MUL_UNIT_WB_ID]));
    endgenerate
    generate if (USE_DIV)
            div_unit div_unit_block (.*, .div_wb(unit_wb[DIV_UNIT_WB_ID]));
    endgenerate

    /*************************************
     * Writeback Mux and Instruction Tracking
     *************************************/
    write_back write_back_mux (.*);

    ////////////////////////////////////////////////////
    //Assertions
    //Ensure that reset is held for at least 32 cycles to clear shift regs
   // always_ff @ (posedge clk) begin
   //     assert property(@(posedge clk) $rose (rst) |=> rst[*32]) else $error("Reset not held for long enough!");
   // end

endmodule
