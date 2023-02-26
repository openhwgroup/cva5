/*
 * Copyright © 2017, 2018, 2019 Eric Matthews,  Lesley Shannon
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



module cva5

    import cva5_config::*;
    import l2_config_and_types::*;
    import riscv_types::*;
    import cva5_types::*;

    #(
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,

        local_memory_interface.master instruction_bram,
        local_memory_interface.master data_bram,

        axi_interface.master m_axi,
        avalon_interface.master m_avalon,
        wishbone_interface.master dwishbone,
        wishbone_interface.master iwishbone,

        l2_requester_interface.master l2,

        input interrupt_t s_interrupt,
        input interrupt_t m_interrupt
        );

    ////////////////////////////////////////////////////
    //Unit ID Assignment
    //Generate Issue IDs based on configuration options
    //Then assigned to a struct for ease in passing to sub modules

    //Units with writeback
    localparam int unsigned ALU_UNIT_ID = 32'd0;
    localparam int unsigned LS_UNIT_ID = 32'd1;
    localparam int unsigned CSR_UNIT_ID = LS_UNIT_ID + int'(CONFIG.INCLUDE_CSRS);
    localparam int unsigned MUL_UNIT_ID = CSR_UNIT_ID + int'(CONFIG.INCLUDE_MUL);
    localparam int unsigned DIV_UNIT_ID = MUL_UNIT_ID + int'(CONFIG.INCLUDE_DIV);
    localparam int unsigned CUSTOM_UNIT_ID = DIV_UNIT_ID + int'(CONFIG.INCLUDE_CUSTOM);
    //Non-writeback units
    localparam int unsigned BRANCH_UNIT_ID = CUSTOM_UNIT_ID + 1;
    localparam int unsigned IEC_UNIT_ID = BRANCH_UNIT_ID + 1;

    //Total number of units
    localparam int unsigned NUM_UNITS = IEC_UNIT_ID + 1; 

    localparam unit_id_param_t UNIT_IDS = '{
        ALU : ALU_UNIT_ID,
        LS : LS_UNIT_ID,
        CSR : CSR_UNIT_ID,
        MUL : MUL_UNIT_ID,
        DIV : DIV_UNIT_ID,
        CUSTOM : CUSTOM_UNIT_ID,
        BR : BRANCH_UNIT_ID,
        IEC : IEC_UNIT_ID
    };

    ////////////////////////////////////////////////////
    //Writeback Port Assignment
    //
    localparam int unsigned NUM_WB_UNITS_GROUP_1 = 1;//ALU
    localparam int unsigned ALU_UNIT_WB1_ID = 32'd0;

    localparam int unsigned NUM_WB_UNITS_GROUP_2 = 1;//LS
    localparam int unsigned LS_UNIT_WB2_ID = 32'd0;

    localparam int unsigned NUM_WB_UNITS_GROUP_3 = int'(CONFIG.INCLUDE_CSRS) + int'(CONFIG.INCLUDE_MUL) + int'(CONFIG.INCLUDE_DIV) + int'(CONFIG.INCLUDE_CUSTOM);
    localparam int unsigned DIV_UNIT_WB3_ID = 32'd0;
    localparam int unsigned MUL_UNIT_WB3_ID = 32'd0 + int'(CONFIG.INCLUDE_DIV);
    localparam int unsigned CSR_UNIT_WB3_ID = 32'd0 + int'(CONFIG.INCLUDE_MUL)+ int'(CONFIG.INCLUDE_DIV);
    localparam int unsigned CUSTOM_UNIT_WB3_ID = 32'd0 + int'(CONFIG.INCLUDE_MUL)+ int'(CONFIG.INCLUDE_DIV) + int'(CONFIG.INCLUDE_CSRS);

    ////////////////////////////////////////////////////
    //Connecting Signals
    l1_arbiter_request_interface l1_request[L1_CONNECTIONS-1:0]();
    l1_arbiter_return_interface l1_response[L1_CONNECTIONS-1:0]();
    logic sc_complete;
    logic sc_success;

    branch_predictor_interface bp();
    branch_results_t br_results;
    logic branch_flush;
    logic potential_branch_exception;
    exception_packet_t br_exception;
    logic branch_exception_is_jump;

    ras_interface ras();

    issue_packet_t issue;
    register_file_issue_interface #(.NUM_WB_GROUPS(CONFIG.NUM_WB_GROUPS)) rf_issue();

    logic [NUM_UNITS-1:0] unit_needed;
    logic [NUM_UNITS-1:0][REGFILE_READ_PORTS-1:0] unit_uses_rs;
    logic [NUM_UNITS-1:0] unit_uses_rd;

    logic [31:0] constant_alu;

    unit_issue_interface unit_issue [NUM_UNITS-1:0]();

    exception_packet_t  ls_exception;
    logic ls_exception_is_store;

    unit_writeback_interface unit_wb1 [NUM_WB_UNITS_GROUP_1]();
    unit_writeback_interface unit_wb2 [NUM_WB_UNITS_GROUP_2]();
    unit_writeback_interface unit_wb3 [NUM_WB_UNITS_GROUP_3 == 0 ? 1 : NUM_WB_UNITS_GROUP_3]();

    mmu_interface immu();
    mmu_interface dmmu();

    tlb_interface itlb();
    tlb_interface dtlb();
    logic tlb_on;
    logic [ASIDLEN-1:0] asid;

    //Instruction ID/Metadata
        //ID issuing
    id_t pc_id;
    logic pc_id_available;
    logic pc_id_assigned;
    logic [31:0] if_pc;
        //Fetch stage
    id_t fetch_id;
    logic fetch_complete;
    logic [31:0] fetch_instruction;
    logic early_branch_flush;
    logic early_branch_flush_ras_adjust;
    fetch_metadata_t fetch_metadata;
        //Decode stage
    logic decode_advance;
    decode_packet_t decode;   
    logic decode_uses_rd;
    rs_addr_t decode_rd_addr;
    exception_sources_t decode_exception_unit;
    logic decode_is_store;
    phys_addr_t decode_phys_rd_addr;
    phys_addr_t decode_phys_rs_addr [REGFILE_READ_PORTS];
    logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] decode_rs_wb_group [REGFILE_READ_PORTS];

        //ID freeing
    retire_packet_t wb_retire;
    retire_packet_t store_retire;
    id_t retire_ids [RETIRE_PORTS];
    id_t retire_ids_next [RETIRE_PORTS];
    logic retire_port_valid [RETIRE_PORTS];
    logic [LOG2_RETIRE_PORTS : 0] retire_count;
        //Writeback
    wb_packet_t wb_packet [CONFIG.NUM_WB_GROUPS];
    phys_addr_t wb_phys_addr [CONFIG.NUM_WB_GROUPS];
         //Exception
    logic [31:0] oldest_pc;

    renamer_interface #(.NUM_WB_GROUPS(CONFIG.NUM_WB_GROUPS)) decode_rename_interface ();

    //Global Control
    exception_interface exception [NUM_EXCEPTION_SOURCES]();
    logic [$clog2(NUM_EXCEPTION_SOURCES)-1:0] current_exception_unit;
    gc_outputs_t gc;
    load_store_status_t load_store_status;
    logic [LOG2_MAX_IDS:0] post_issue_count;

    logic [1:0] current_privilege;
    logic mret;
    logic sret;
    logic [31:0] epc;
    logic [31:0] exception_target_pc;

    logic interrupt_taken;
    logic interrupt_pending;

    logic processing_csr;

    //Decode Unit and Fetch Unit
    logic issue_stage_ready;
    phys_addr_t issue_phys_rs_addr [REGFILE_READ_PORTS];
    rs_addr_t issue_rs_addr [REGFILE_READ_PORTS];
    logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] issue_rd_wb_group;
    logic illegal_instruction;
    logic instruction_issued;
    logic instruction_issued_with_rd;

    ////////////////////////////////////////////////////
    //Implementation


    ////////////////////////////////////////////////////
    // Memory Interface
    generate if (CONFIG.INCLUDE_S_MODE || CONFIG.INCLUDE_ICACHE || CONFIG.INCLUDE_DCACHE) begin : gen_l1_arbiter
        l1_arbiter #(.CONFIG(CONFIG))
        arb(
            .clk (clk),
            .rst (rst),
            .l2 (l2),
            .sc_complete (sc_complete),
            .sc_success (sc_success),
            .l1_request (l1_request),
            .l1_response (l1_response)
        );
    end
    endgenerate

    ////////////////////////////////////////////////////
    // ID support
    instruction_metadata_and_id_management #(.CONFIG(CONFIG))
    id_block (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .pc_id (pc_id),
        .pc_id_available (pc_id_available),
        .if_pc (if_pc),
        .pc_id_assigned (pc_id_assigned),
        .fetch_id (fetch_id),
        .early_branch_flush (early_branch_flush),
        .fetch_complete (fetch_complete),
        .fetch_instruction (fetch_instruction),
        .fetch_metadata (fetch_metadata),
        .decode (decode),
        .decode_advance (decode_advance),
        .decode_uses_rd (decode_uses_rd),
        .decode_rd_addr (decode_rd_addr),
        .decode_phys_rd_addr (decode_phys_rd_addr),
        .decode_exception_unit (decode_exception_unit),
        .decode_is_store (decode_is_store),
        .issue (issue),
        .instruction_issued (instruction_issued),
        .instruction_issued_with_rd (instruction_issued_with_rd),
        .wb_packet (wb_packet),
        .wb_phys_addr (wb_phys_addr),
        .wb_retire (wb_retire),
        .store_retire (store_retire),
        .retire_ids (retire_ids),
        .retire_ids_next (retire_ids_next),
        .retire_port_valid(retire_port_valid),
        .retire_count (retire_count),
        .post_issue_count(post_issue_count),
        .oldest_pc (oldest_pc),
        .current_exception_unit (current_exception_unit)
    );

    ////////////////////////////////////////////////////
    // Fetch
    fetch # (.CONFIG(CONFIG))
    fetch_block (
        .clk (clk),
        .rst (rst),
        .branch_flush (branch_flush),
        .gc (gc),
        .pc_id (pc_id),
        .pc_id_available (pc_id_available),
        .pc_id_assigned (pc_id_assigned),
        .fetch_complete (fetch_complete),
        .fetch_metadata (fetch_metadata),
        .bp (bp),
        .ras (ras),
        .early_branch_flush (early_branch_flush),
        .early_branch_flush_ras_adjust (early_branch_flush_ras_adjust),
        .if_pc (if_pc),
        .fetch_instruction (fetch_instruction),                                
        .instruction_bram (instruction_bram), 
        .iwishbone (iwishbone),
        .icache_on ('1),
        .tlb (itlb), 
        .tlb_on (tlb_on),
        .l1_request (l1_request[L1_ICACHE_ID]), 
        .l1_response (l1_response[L1_ICACHE_ID]), 
        .exception (1'b0)
    );

    branch_predictor #(.CONFIG(CONFIG))
    bp_block (       
        .clk (clk),
        .rst (rst),
        .bp (bp),
        .br_results (br_results),
        .ras (ras)
    );

    ras # (.CONFIG(CONFIG))
    ras_block(
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .early_branch_flush_ras_adjust (early_branch_flush_ras_adjust),
        .ras (ras)
    );

    generate if (CONFIG.INCLUDE_S_MODE) begin : gen_itlb_immu

        tlb_lut_ram #(.WAYS(CONFIG.ITLB.WAYS), .DEPTH(CONFIG.ITLB.DEPTH))
        i_tlb (       
            .clk (clk),
            .rst (rst),
            .gc (gc),
            .abort_request (gc.fetch_flush | early_branch_flush),
            .asid (asid),
            .tlb (itlb), 
            .mmu (immu)
        );

        mmu i_mmu (
            .clk (clk),
            .rst (rst),
            .mmu (immu) , 
            .abort_request (gc.fetch_flush),
            .l1_request (l1_request[L1_IMMU_ID]), 
            .l1_response (l1_response[L1_IMMU_ID])
        );

        end
        else begin
            assign itlb.ready = 1;
            assign itlb.done = itlb.new_request;
            assign itlb.physical_address = itlb.virtual_address;
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Renamer
    renamer #(.CONFIG(CONFIG)) 
    renamer_block (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .decode_advance (decode_advance),
        .decode (decode_rename_interface),
        .issue (issue), //packet
        .instruction_issued_with_rd (instruction_issued_with_rd),
        .wb_retire (wb_retire)
    );

    ////////////////////////////////////////////////////
    //Decode/Issue
    decode_and_issue #(
        .CONFIG (CONFIG),
        .NUM_UNITS (NUM_UNITS),
        .UNIT_IDS (UNIT_IDS)
        )
    decode_and_issue_block (
        .clk (clk),
        .rst (rst),
        .pc_id_available (pc_id_available),
        .decode (decode),
        .decode_advance (decode_advance),
        .unit_needed (unit_needed),
        .unit_uses_rs (unit_uses_rs),
        .unit_uses_rd (unit_uses_rd),
        .renamer (decode_rename_interface),
        .decode_uses_rd (decode_uses_rd),
        .decode_rd_addr (decode_rd_addr),
        .decode_exception_unit (decode_exception_unit),
        .decode_phys_rd_addr (decode_phys_rd_addr),
        .decode_phys_rs_addr (decode_phys_rs_addr),
        .decode_rs_wb_group (decode_rs_wb_group),
        .instruction_issued (instruction_issued),
        .instruction_issued_with_rd (instruction_issued_with_rd),
        .issue (issue),
        .issue_rs_addr (issue_rs_addr),
        .issue_stage_ready (issue_stage_ready),
        .issue_phys_rs_addr (issue_phys_rs_addr),
        .issue_rd_wb_group (issue_rd_wb_group),
        .rf (rf_issue),
        .constant_alu (constant_alu),
        .unit_issue (unit_issue),
        .gc (gc),
        .current_privilege (current_privilege),
        .exception (exception[PRE_ISSUE_EXCEPTION])
    );

    ////////////////////////////////////////////////////
    //Register File
    register_file #(.CONFIG(CONFIG))
    register_file_block (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .decode_phys_rs_addr (decode_phys_rs_addr),
        .decode_phys_rd_addr (decode_phys_rd_addr),
        .decode_rs_wb_group (decode_rs_wb_group),
        .decode_advance (decode_advance),
        .decode_uses_rd (decode_uses_rd),
        .decode_rd_addr (decode_rd_addr),
        .rf_issue (rf_issue),
        .commit (wb_packet),
        .wb_phys_addr (wb_phys_addr)
    );

    ////////////////////////////////////////////////////
    //Execution Units
    branch_unit #(.CONFIG(CONFIG))
    branch_unit_block ( 
        .clk (clk),
        .rst (rst),
        .decode_stage (decode),
        .issue_stage (issue),
        .issue_stage_ready (issue_stage_ready),
        .unit_needed (unit_needed[UNIT_IDS.BR]),
        .uses_rs (unit_uses_rs[UNIT_IDS.BR]),
        .uses_rd (unit_uses_rd[UNIT_IDS.BR]),
        .rf (rf_issue.data),
        .constant_alu (constant_alu),
        .issue (unit_issue[UNIT_IDS.BR]),
        .br_results (br_results),
        .branch_flush (branch_flush),
        .exception (exception[BR_EXCEPTION])
    );


    alu_unit alu_unit_block (
        .clk (clk),
        .rst (rst),
        .decode_stage (decode),
        .issue_stage (issue),
        .issue_stage_ready (issue_stage_ready),
        .unit_needed (unit_needed[UNIT_IDS.ALU]),
        .uses_rs (unit_uses_rs[UNIT_IDS.ALU]),
        .uses_rd (unit_uses_rd[UNIT_IDS.ALU]),
        .rf (rf_issue.data),
        .constant_alu (constant_alu),
        .issue_rs_addr (issue_rs_addr),
        .issue (unit_issue[UNIT_IDS.ALU]), 
        .wb (unit_wb1[ALU_UNIT_WB1_ID])
    );

    load_store_unit #(.CONFIG(CONFIG))
    load_store_unit_block (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .decode_stage (decode),
        .issue_stage (issue),
        .issue_stage_ready (issue_stage_ready),
        .unit_needed (unit_needed[UNIT_IDS.LS]),
        .uses_rs (unit_uses_rs[UNIT_IDS.LS]),
        .uses_rd (unit_uses_rd[UNIT_IDS.LS]),
        .decode_is_store (decode_is_store),
        .instruction_issued_with_rd (instruction_issued_with_rd),
        .issue_rs_addr (issue_rs_addr),
        .issue_rd_wb_group (issue_rd_wb_group),
        .rs2_inuse (rf_issue.inuse[RS2]),
        .rf (rf_issue.data),
        .issue (unit_issue[UNIT_IDS.LS]),
        .dcache_on (1'b1), 
        .clear_reservation (1'b0), 
        .tlb (dtlb),
        .tlb_on (tlb_on),                            
        .l1_request (l1_request[L1_DCACHE_ID]), 
        .l1_response (l1_response[L1_DCACHE_ID]),
        .sc_complete (sc_complete),
        .sc_success (sc_success),                                       
        .m_axi (m_axi),
        .m_avalon (m_avalon),
        .dwishbone (dwishbone),                                       
        .data_bram (data_bram),
        .wb_packet (wb_packet),
        .store_retire (store_retire),
        .exception (exception[LS_EXCEPTION]),
        .load_store_status(load_store_status),
        .wb (unit_wb2[LS_UNIT_WB2_ID])
    );

    generate if (CONFIG.INCLUDE_S_MODE) begin : gen_dtlb_dmmu
        tlb_lut_ram #(.WAYS(CONFIG.DTLB.WAYS), .DEPTH(CONFIG.DTLB.DEPTH))
        d_tlb (       
            .clk (clk),
            .rst (rst),
            .gc (gc),
            .abort_request (1'b0),
            .asid (asid),
            .tlb (dtlb), 
            .mmu (dmmu)
        );

        mmu d_mmu (
            .clk (clk),
            .rst (rst),
            .mmu (dmmu) , 
            .abort_request (1'b0),
            .l1_request (l1_request[L1_DMMU_ID]), 
            .l1_response (l1_response[L1_DMMU_ID])
        );
    end
    else begin
            assign dtlb.ready = 1;
            assign dtlb.done = dtlb.new_request;
            assign dtlb.physical_address = dtlb.virtual_address;
    end
    endgenerate

    generate if (CONFIG.INCLUDE_CSRS) begin : gen_csrs
        csr_unit # (.CONFIG(CONFIG))
        csr_unit_block (
            .clk(clk),
            .rst(rst),
            .decode_stage (decode),
            .issue_stage (issue),
            .issue_stage_ready (issue_stage_ready),
            .issue_rs_addr (issue_rs_addr),
            .unit_needed (unit_needed[UNIT_IDS.CSR]),
            .uses_rs (unit_uses_rs[UNIT_IDS.CSR]),
            .uses_rd (unit_uses_rd[UNIT_IDS.CSR]),
            .rf (rf_issue.data),
            .issue (unit_issue[UNIT_IDS.CSR]), 
            .wb (unit_wb3[CSR_UNIT_WB3_ID]),
            .current_privilege(current_privilege),
            .interrupt_taken(interrupt_taken),
            .interrupt_pending(interrupt_pending),
            .processing_csr(processing_csr),
            .tlb_on(tlb_on),
            .asid(asid),
            .immu(immu),
            .dmmu(dmmu),
            .exception(gc.exception),
            .exception_target_pc (exception_target_pc),
            .mret(mret),
            .sret(sret),
            .epc(epc),
            .wb_retire (wb_retire),
            .retire_ids(retire_ids),
            .retire_count (retire_count),
            .s_interrupt(s_interrupt),
            .m_interrupt(m_interrupt)
        );
    end endgenerate

    gc_unit #(.CONFIG(CONFIG))
    gc_unit_block (
        .clk (clk),
        .rst (rst),
        .decode_stage (decode),
        .issue_stage (issue),
        .issue_stage_ready (issue_stage_ready),
        .unit_needed (unit_needed[UNIT_IDS.IEC]),
        .uses_rs (unit_uses_rs[UNIT_IDS.IEC]),
        .uses_rd (unit_uses_rd[UNIT_IDS.IEC]),
        .constant_alu (constant_alu),
        .rf (rf_issue.data),
        .issue (unit_issue[UNIT_IDS.IEC]),
        .branch_flush (branch_flush),
        .exception (exception),
        .exception_target_pc (exception_target_pc),
        .current_exception_unit (current_exception_unit),
        .gc (gc),
        .oldest_pc (oldest_pc),
        .mret(mret),
        .sret(sret),
        .epc(epc),
        .wb_retire (wb_retire),
        .retire_ids (retire_ids),
        .retire_ids_next (retire_ids_next),
        .interrupt_taken(interrupt_taken),
        .interrupt_pending(interrupt_pending),
        .processing_csr(processing_csr),
        .load_store_status(load_store_status),
        .post_issue_count (post_issue_count)
    );

    generate if (CONFIG.INCLUDE_MUL) begin : gen_mul
        mul_unit mul_unit_block (
            .clk (clk),
            .rst (rst),
            .decode_stage (decode),
            .issue_stage (issue),
            .issue_stage_ready (issue_stage_ready),
            .unit_needed (unit_needed[UNIT_IDS.MUL]),
            .uses_rs (unit_uses_rs[UNIT_IDS.MUL]),
            .uses_rd (unit_uses_rd[UNIT_IDS.MUL]),
            .rf (rf_issue.data),
            .issue (unit_issue[UNIT_IDS.MUL]),
            .wb (unit_wb3[MUL_UNIT_WB3_ID])
        );
    end endgenerate

    generate if (CONFIG.INCLUDE_DIV) begin : gen_div
        div_unit div_unit_block (
            .clk (clk),
            .rst (rst),
            .gc (gc),
            .instruction_issued_with_rd (instruction_issued_with_rd),
            .decode_stage (decode),
            .issue_stage (issue),
            .issue_stage_ready (issue_stage_ready),
            .issue_rs_addr (issue_rs_addr),
            .unit_needed (unit_needed[UNIT_IDS.DIV]),
            .uses_rs (unit_uses_rs[UNIT_IDS.DIV]),
            .uses_rd (unit_uses_rd[UNIT_IDS.DIV]),
            .rf (rf_issue.data),
            .issue (unit_issue[UNIT_IDS.DIV]), 
            .wb (unit_wb3[DIV_UNIT_WB3_ID])
        );
    end endgenerate


    generate if (CONFIG.INCLUDE_CUSTOM) begin : gen_custom
        custom_unit custom_unit_block (
            .clk (clk),
            .rst (rst),
            .decode_stage (decode),
            .unit_needed (unit_needed[UNIT_IDS.CUSTOM]),
            .uses_rs (unit_uses_rs[UNIT_IDS.CUSTOM]),
            .uses_rd (unit_uses_rd[UNIT_IDS.CUSTOM]),
            .issue_stage (issue),
            .issue_stage_ready (issue_stage_ready),
            .rf (rf_issue.data),
            .issue (unit_issue[UNIT_IDS.CUSTOM]), 
            .wb (unit_wb3[CUSTOM_UNIT_WB3_ID])
        );
    end endgenerate

    ////////////////////////////////////////////////////
    //Writeback
    //First writeback port: ALU
    //Second writeback port: LS, CSR, [MUL], [DIV]
    writeback #(
        .CONFIG (CONFIG),
        .NUM_WB_UNITS (NUM_WB_UNITS_GROUP_1)
    )
    writeback_block1 (
        .clk (clk),
        .rst (rst),
        .wb_packet (wb_packet[0]),
        .unit_wb (unit_wb1)
    );
    writeback #(
        .CONFIG (CONFIG),
        .NUM_WB_UNITS (NUM_WB_UNITS_GROUP_2)
    )
    writeback_block2 (
        .clk (clk),
        .rst (rst),
        .wb_packet (wb_packet[1]),
        .unit_wb (unit_wb2)
    );

    generate if (NUM_WB_UNITS_GROUP_3 > 0) begin : gen_wb3
        writeback #(
            .CONFIG (CONFIG),
            .NUM_WB_UNITS (NUM_WB_UNITS_GROUP_3)
        )
        writeback_block3 (
            .clk (clk),
            .rst (rst),
            .wb_packet (wb_packet[2]),
            .unit_wb (unit_wb3)
        );
    end endgenerate
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    //Ensure that reset is held for at least 32 cycles to clear shift regs
    // always_ff @ (posedge clk) begin
    //     assert property(@(posedge clk) $rose (rst) |=> rst[*32]) else $error("Reset not held for long enough!");
    // end

    ////////////////////////////////////////////////////
    //Assertions


endmodule
