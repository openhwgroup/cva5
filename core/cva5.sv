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

        output trace_outputs_t tr,

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
    //Non-writeback units
    localparam int unsigned BRANCH_UNIT_ID = DIV_UNIT_ID + 1;
    localparam int unsigned IEC_UNIT_ID = BRANCH_UNIT_ID + 1;

    //Total number of units
    localparam int unsigned NUM_UNITS = IEC_UNIT_ID + 1; 

    localparam unit_id_param_t UNIT_IDS = '{
        ALU : ALU_UNIT_ID,
        LS : LS_UNIT_ID,
        CSR : CSR_UNIT_ID,
        MUL : MUL_UNIT_ID,
        DIV : DIV_UNIT_ID,
        BR : BRANCH_UNIT_ID,
        IEC : IEC_UNIT_ID
    };

    ////////////////////////////////////////////////////
    //Writeback Port Assignment
    //
    localparam int unsigned NUM_WB_UNITS_GROUP_1 = 1;//ALU
    localparam int unsigned NUM_WB_UNITS_GROUP_2 = 1 + int'(CONFIG.INCLUDE_CSRS) + int'(CONFIG.INCLUDE_MUL) + int'(CONFIG.INCLUDE_DIV);//LS
    localparam int unsigned NUM_WB_UNITS = NUM_WB_UNITS_GROUP_1 + NUM_WB_UNITS_GROUP_2;

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


    alu_inputs_t alu_inputs;
    load_store_inputs_t ls_inputs;
    branch_inputs_t branch_inputs;
    mul_inputs_t mul_inputs;
    div_inputs_t div_inputs;
    gc_inputs_t gc_inputs;
    csr_inputs_t csr_inputs;

    unit_issue_interface unit_issue [NUM_UNITS-1:0]();

    exception_packet_t  ls_exception;
    logic ls_exception_is_store;

    unit_writeback_interface unit_wb  [NUM_WB_UNITS]();

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
    phys_addr_t decode_phys_rd_addr;
    phys_addr_t decode_phys_rs_addr [REGFILE_READ_PORTS];
    logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] decode_rs_wb_group [REGFILE_READ_PORTS];

        //ID freeing
    retire_packet_t retire;
    id_t retire_ids [RETIRE_PORTS];
    id_t retire_ids_next [RETIRE_PORTS];
    logic retire_port_valid [RETIRE_PORTS];
        //Writeback
    wb_packet_t wb_packet [CONFIG.NUM_WB_GROUPS];
    commit_packet_t commit_packet [CONFIG.NUM_WB_GROUPS];
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
    logic illegal_instruction;
    logic instruction_issued;
    logic instruction_issued_with_rd;

    //LS
    wb_packet_t wb_snoop;

    //Trace Interface Signals
    logic tr_early_branch_correction;
    logic tr_operand_stall;
    logic tr_unit_stall;
    logic tr_no_id_stall;
    logic tr_no_instruction_stall;
    logic tr_other_stall;
    logic tr_branch_operand_stall;
    logic tr_alu_operand_stall;
    logic tr_ls_operand_stall;
    logic tr_div_operand_stall;

    logic tr_alu_op;
    logic tr_branch_or_jump_op;
    logic tr_load_op;
    logic tr_store_op;
    logic tr_mul_op;
    logic tr_div_op;
    logic tr_misc_op;

    logic tr_instruction_issued_dec;
    logic [31:0] tr_instruction_pc_dec;
    logic [31:0] tr_instruction_data_dec;

    logic tr_branch_correct;
    logic tr_branch_misspredict;
    logic tr_return_correct;
    logic tr_return_misspredict;

    logic tr_load_conflict_delay;

    logic tr_rs1_forwarding_needed;
    logic tr_rs2_forwarding_needed;
    logic tr_rs1_and_rs2_forwarding_needed;

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
        .issue (issue),
        .instruction_issued (instruction_issued),
        .instruction_issued_with_rd (instruction_issued_with_rd),
        .wb_packet (wb_packet),
        .commit_packet (commit_packet),
        .retire (retire),
        .retire_ids (retire_ids),
        .retire_ids_next (retire_ids_next),
        .retire_port_valid(retire_port_valid),
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
        .exception (1'b0),
        .tr_early_branch_correction (tr_early_branch_correction)
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
        .retire (retire) //packet
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
        .rf (rf_issue),
        .alu_inputs (alu_inputs),
        .ls_inputs (ls_inputs),
        .branch_inputs (branch_inputs),
        .gc_inputs (gc_inputs),
        .csr_inputs (csr_inputs),
        .mul_inputs (mul_inputs),
        .div_inputs (div_inputs),
        .unit_issue (unit_issue),
        .gc (gc),
        .current_privilege (current_privilege),
        .exception (exception[PRE_ISSUE_EXCEPTION]),
        .tr_operand_stall (tr_operand_stall),
        .tr_unit_stall (tr_unit_stall),
        .tr_no_id_stall (tr_no_id_stall),
        .tr_no_instruction_stall (tr_no_instruction_stall),
        .tr_other_stall (tr_other_stall),
        .tr_branch_operand_stall (tr_branch_operand_stall),
        .tr_alu_operand_stall (tr_alu_operand_stall),
        .tr_ls_operand_stall (tr_ls_operand_stall),
        .tr_div_operand_stall (tr_div_operand_stall),
        .tr_alu_op (tr_alu_op),
        .tr_branch_or_jump_op (tr_branch_or_jump_op),
        .tr_load_op (tr_load_op),
        .tr_store_op (tr_store_op),
        .tr_mul_op (tr_mul_op),
        .tr_div_op (tr_div_op),
        .tr_misc_op (tr_misc_op),
        .tr_instruction_issued_dec (tr_instruction_issued_dec),
        .tr_instruction_pc_dec (tr_instruction_pc_dec),
        .tr_instruction_data_dec (tr_instruction_data_dec)
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
        .rf_issue (rf_issue),
        .commit (commit_packet)
    );

    ////////////////////////////////////////////////////
    //Execution Units
    branch_unit #(.CONFIG(CONFIG))
    branch_unit_block ( 
        .clk (clk),
        .rst (rst),                                    
        .issue (unit_issue[UNIT_IDS.BR]),
        .branch_inputs (branch_inputs),
        .br_results (br_results),
        .branch_flush (branch_flush),
        .exception (exception[BR_EXCEPTION]),
        .tr_branch_correct (tr_branch_correct),
        .tr_branch_misspredict (tr_branch_misspredict),
        .tr_return_correct (tr_return_correct),
        .tr_return_misspredict (tr_return_misspredict)
    );


    alu_unit alu_unit_block (
        .clk (clk),
        .rst (rst),
        .alu_inputs (alu_inputs),
        .issue (unit_issue[UNIT_IDS.ALU]), 
        .wb (unit_wb[UNIT_IDS.ALU])
    );

    load_store_unit #(.CONFIG(CONFIG))
    load_store_unit_block (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .ls_inputs (ls_inputs),
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
        .wb_snoop (wb_snoop),
        .retire_ids (retire_ids),
        .retire_port_valid(retire_port_valid),
        .exception (exception[LS_EXCEPTION]),
        .load_store_status(load_store_status),
        .wb (unit_wb[UNIT_IDS.LS]),
        .tr_load_conflict_delay (tr_load_conflict_delay)
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
            .csr_inputs (csr_inputs),
            .issue (unit_issue[UNIT_IDS.CSR]), 
            .wb (unit_wb[UNIT_IDS.CSR]),
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
            .retire(retire),
            .retire_ids(retire_ids),
            .s_interrupt(s_interrupt),
            .m_interrupt(m_interrupt)
        );
    end endgenerate

    gc_unit #(.CONFIG(CONFIG))
    gc_unit_block (
        .clk (clk),
        .rst (rst),
        .issue (unit_issue[UNIT_IDS.IEC]),
        .gc_inputs (gc_inputs),
        .branch_flush (branch_flush),
        .exception (exception),
        .exception_target_pc (exception_target_pc),
        .current_exception_unit (current_exception_unit),
        .gc (gc),
        .oldest_pc (oldest_pc),
        .mret(mret),
        .sret(sret),
        .epc(epc),
        .retire (retire),
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
            .mul_inputs (mul_inputs),
            .issue (unit_issue[UNIT_IDS.MUL]),
            .wb (unit_wb[UNIT_IDS.MUL])
        );
    end endgenerate

    generate if (CONFIG.INCLUDE_DIV) begin : gen_div
        div_unit div_unit_block (
            .clk (clk),
            .rst (rst),
            .div_inputs (div_inputs),
            .issue (unit_issue[UNIT_IDS.DIV]), 
            .wb (unit_wb[UNIT_IDS.DIV])
        );
    end endgenerate

    ////////////////////////////////////////////////////
    //Writeback
    //First writeback port: ALU
    //Second writeback port: LS, CSR, [MUL], [DIV]
    localparam int unsigned NUM_UNITS_PER_PORT [CONFIG.NUM_WB_GROUPS] = '{NUM_WB_UNITS_GROUP_1, NUM_WB_UNITS_GROUP_2};
    writeback #(
        .CONFIG (CONFIG),
        .NUM_UNITS (NUM_UNITS_PER_PORT),
        .NUM_WB_UNITS (NUM_WB_UNITS)
    )
    writeback_block (
        .clk (clk),
        .rst (rst),
        .wb_packet (wb_packet),
        .unit_wb (unit_wb),
        .wb_snoop (wb_snoop)
    );

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

    ////////////////////////////////////////////////////
    //Trace Interface
    generate if (ENABLE_TRACE_INTERFACE) begin : gen_cva5_trace
        always_ff @(posedge clk) begin
            tr.events.early_branch_correction <= tr_early_branch_correction;
            tr.events.operand_stall <= tr_operand_stall;
            tr.events.unit_stall <= tr_unit_stall;
            tr.events.no_id_stall <= tr_no_id_stall;
            tr.events.no_instruction_stall <= tr_no_instruction_stall;
            tr.events.other_stall <= tr_other_stall;
            tr.events.instruction_issued_dec <= tr_instruction_issued_dec;
            tr.events.branch_operand_stall <= tr_branch_operand_stall;
            tr.events.alu_operand_stall <= tr_alu_operand_stall;
            tr.events.ls_operand_stall <= tr_ls_operand_stall;
            tr.events.div_operand_stall <= tr_div_operand_stall;
            tr.events.alu_op <= tr_alu_op;
            tr.events.branch_or_jump_op <= tr_branch_or_jump_op;
            tr.events.load_op <= tr_load_op;
            tr.events.store_op <= tr_store_op;
            tr.events.mul_op <= tr_mul_op;
            tr.events.div_op <= tr_div_op;
            tr.events.misc_op <= tr_misc_op;
            tr.events.branch_correct <= tr_branch_correct;
            tr.events.branch_misspredict <= tr_branch_misspredict;
            tr.events.return_correct <= tr_return_correct;
            tr.events.return_misspredict <= tr_return_misspredict;
            tr.events.load_conflict_delay <= tr_load_conflict_delay;
            tr.events.rs1_forwarding_needed <= tr_rs1_forwarding_needed;
            tr.events.rs2_forwarding_needed <= tr_rs2_forwarding_needed;
            tr.events.rs1_and_rs2_forwarding_needed <= tr_rs1_and_rs2_forwarding_needed;
            tr.instruction_pc_dec <= tr_instruction_pc_dec;
            tr.instruction_data_dec <= tr_instruction_data_dec;
        end
    end
    endgenerate

endmodule
