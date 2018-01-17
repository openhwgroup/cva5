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

        bram_interface.user instruction_bram,
        bram_interface.user data_bram,

        axi_interface.master m_axi,
        avalon_interface.master m_avalon,

        l2_requester_interface.requester l2,

        input logic interrupt,

        //debug
        output logic[31:0] if2_pc_debug,
        output logic[31:0] dec_pc_debug

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
    csr_inputs_t csr_inputs;

    func_unit_ex_interface branch_ex();
    func_unit_ex_interface alu_ex();
    func_unit_ex_interface ls_ex();
    func_unit_ex_interface csr_ex();
    func_unit_ex_interface mul_ex();
    func_unit_ex_interface div_ex();


    instruction_buffer_interface ib();
    inflight_queue_interface iq();
    id_generator_interface id_gen();

    unit_writeback_interface unit_wb [NUM_WB_UNITS-1:0]();

    //writeback_unit_interface unit_wb();

    register_file_writeback_interface rf_wb();

    csr_exception_interface csr_exception();

    tlb_interface itlb();
    tlb_interface dtlb();
    logic tlb_on;
    logic [9:0] asid;
    logic return_from_exception;

    mmu_interface immu();
    mmu_interface dmmu();

    logic inorder;


    //Branch Unit and Fetch Unit
    logic branch_taken;
    logic [31:0] pc_offset;
    logic[31:0] jalr_rs1;
    logic jalr;

    //Decode Unit and Fetch Unit
    logic [31:0] if2_pc;
    logic [31:0] instruction;
    logic dec_advance;
    logic flush;
    logic illegal_instruction;

    logic [31:0] dec_pc;
    logic [31:0] pc_ex;

    logic instruction_issued_no_rd;
    logic instruction_complete;

    assign instruction_issued = dec_advance;


    assign if2_pc_debug = if2_pc;
    assign dec_pc_debug = dec_pc;


    /*************************************
     * Memory Interface
     *************************************/
    generate if (USE_MMU || USE_ICACHE || USE_DCACHE)
            l1_arbiter arb(.*);
    endgenerate

    /*************************************
     * CPU Front end
     *************************************/
    fetch fetch_block (.*, .icache_on('1), .tlb(itlb), .l1_request(l1_request[L1_ICACHE_ID]), .l1_response(l1_response[L1_ICACHE_ID]), .exception(1'b0));
    branch_table bt_block (.*);
    ras ras_block(.*);
    generate if (USE_MMU) begin
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
     * Decode/Issue/Control
     *************************************/
    decode decode_block (.*);
    register_file register_file_block (.*);
    id_generator id_gen_block (.*);
    inflight_queue inst_queue(.*);

    /*************************************
     * Units
     *************************************/
    branch_unit branch_unit_block (.*, .branch_wb(unit_wb[BRANCH_UNIT_ID].unit));
    alu_unit alu_unit_block (.*, .alu_wb(unit_wb[ALU_UNIT_ID].unit));

//    genvar i;
//    generate
//        for (i = 0; i < 5; i++) begin
//            alu_unit single_cycle_accelerators (.*, .alu_ex(single_accel), .alu_wb(unit_wb[ACCEL+i].unit));
//        end
//    endgenerate
//
    load_store_unit load_store_unit_block (.*, .dcache_on(1'b1), .clear_reservation(1'b0), .tlb(dtlb), .ls_wb(unit_wb[LS_UNIT_ID].unit), .l1_request(l1_request[L1_DCACHE_ID]), .l1_response(l1_response[L1_DCACHE_ID]));
    generate if (USE_MMU) begin
            tlb_lut_ram #(DTLB_WAYS, DTLB_DEPTH) d_tlb (.*, .tlb(dtlb), .mmu(dmmu));
            mmu d_mmu (.*, .mmu(dmmu), .l1_request(l1_request[L1_DMMU_ID]), .l1_response(l1_response[L1_DMMU_ID]), .mmu_exception());
        end
        else begin
            assign dtlb.complete = 1;
            assign dtlb.physical_address = dtlb.virtual_address;
        end
    endgenerate
    csr_unit csr_unit_block (.*, .csr_wb(unit_wb[CSR_UNIT_ID].unit));
    generate if (USE_MUL)
            mul_unit mul_unit_block (.*, .mul_wb(unit_wb[MUL_UNIT_ID].unit));
    endgenerate
    generate if (USE_DIV)
            div_unit div_unit_block (.*, .div_wb(unit_wb[DIV_UNIT_ID].unit));
    endgenerate

    /*************************************
     * Writeback Mux
     *************************************/
    write_back write_back_mux (.*);

endmodule
