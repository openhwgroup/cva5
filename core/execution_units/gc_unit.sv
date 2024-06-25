/*
 * Copyright © 2018 Eric Matthews,  Lesley Shannon
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

module gc_unit

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    import csr_types::*;
    import opcodes::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,

        //Decode
        input decode_packet_t decode_stage,
        output logic unit_needed,
        output logic [REGFILE_READ_PORTS-1:0] uses_rs,
        output logic uses_rd,

        input issue_packet_t issue_stage,
        input logic issue_stage_ready,
        input logic instruction_issued,
        input logic [31:0] constant_alu,
        input logic [31:0] rf [REGFILE_READ_PORTS],

        unit_issue_interface.unit issue,

        //Branch miss predict
        input logic branch_flush,

        //Exception
        exception_interface.econtrol exception [NUM_EXCEPTION_SOURCES],
        input logic [31:0] exception_target_pc,

        output logic mret,
        output logic sret,
        input logic [31:0] epc,

        //CSR Interrupts
        input logic interrupt_pending,
        output logic interrupt_taken,

        //CSR front end flush
        input logic csr_frontend_flush,

        //Output controls
        output gc_outputs_t gc,

        //Ordering support
        input load_store_status_t load_store_status,
        input logic [LOG2_MAX_IDS:0] post_issue_count
    );

    //Largest depth for TLBs
    localparam int TLB_CLEAR_DEPTH = (CONFIG.DTLB.DEPTH > CONFIG.ITLB.DEPTH) ? CONFIG.DTLB.DEPTH : CONFIG.ITLB.DEPTH;
    //For general reset clear, greater of TLB depth or id-flight memory blocks (MAX_IDS)
    localparam int INIT_CLEAR_DEPTH = CONFIG.INCLUDE_S_MODE ? (TLB_CLEAR_DEPTH > 64 ? TLB_CLEAR_DEPTH : 64) : 64;

    ////////////////////////////////////////////////////
    //Overview
    //All CSR instructions hold the issue stage until they are the oldest instruction and complete.
    //  As such, their values are known at issue time for any call/ret instruction.

    //FENCE.I:
    //    flush and hold fetch until L/S unit empty
    //    Local mem (nothing extra required for coherency)
    //    Caches, currently not supported.  Requires L2 monitoring.  Need to know that all previous stores from this processor
    //       have been sent out as potential invalidations and ack-ed before fetch can resume
    //SFENCE
    //    flush and hold fetch, wait until L/S input FIFO empty, hold fetch until TLB update complete
    //ECALL, EBREAK, SRET, MRET:
    //    flush fetch, hold until oldest instruction

    //Interrupt
    //wait until issue/execute exceptions are no longer possible, flush fetch, take exception

    //Fetch Exception (TLB and MMU) (fetch stage)
    //flush fetch, wait until issue/execute exceptions are no longer possible, take exception.  If decode stage or later exception occurs first, exception is overridden

    //Illegal opcode (issue stage)
    //fetch flush, take exception.  If execute or later exception occurs first, exception is overridden

    //Branch exceptions (issue/execute stage)
    //fetch flush, take exception.

    //CSR exceptions (issue/execute stage)
    //fetch flush, take exception.

    //LS exceptions (miss-aligned, TLB and MMU) (issue stage)
    //fetch flush, take exception. If execute or later exception occurs first, exception is overridden
    common_instruction_t instruction;//rs1_addr, rs2_addr, fn3, fn7, rd_addr, upper/lower opcode
    typedef enum {RST_STATE, PRE_CLEAR_STATE, INIT_CLEAR_STATE, IDLE_STATE, TLB_CLEAR_STATE, WAIT_INTERRUPT, PRE_ISSUE_FLUSH, WAIT_WRITE} gc_state;
    gc_state state;
    gc_state next_state;

    logic init_clear_done;
    logic tlb_clear_done;

    //GC registered global outputs
    logic gc_init_clear;
    logic gc_fetch_hold;
    logic gc_issue_hold;
    logic gc_fetch_flush;
    logic gc_fetch_ifence;
    logic gc_tlb_flush;
    logic gc_pc_override;
    logic [31:0] gc_pc;

    logic possible_exception;

    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Decode
    logic [31:0] pc_p4;
    logic is_ifence;
    logic is_sfence;
    logic trivial_sfence;
    logic asid_sfence;
    logic is_mret;
    logic is_sret;
    logic is_wfi;

    assign instruction = decode_stage.instruction;

    assign unit_needed =
        (CONFIG.INCLUDE_M_MODE & instruction inside {MRET, WFI}) |
        (CONFIG.INCLUDE_S_MODE & instruction inside {SRET, SFENCE_VMA}) |
        (CONFIG.INCLUDE_IFENCE & instruction inside {FENCE_I});
    always_comb begin
        uses_rs = '0;
        uses_rs[RS1] = CONFIG.INCLUDE_S_MODE & instruction inside {SFENCE_VMA};
        uses_rs[RS2] = CONFIG.INCLUDE_S_MODE & instruction inside {SFENCE_VMA};
        uses_rd = 0;
    end

    //TODO: use mutually exclusive bits to make decoding cheaper
    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            is_ifence <= (instruction.upper_opcode == FENCE_T) & CONFIG.INCLUDE_IFENCE;
            is_sfence <= (instruction.upper_opcode == SYSTEM_T) & (instruction[31:20] == SFENCE_imm) & CONFIG.INCLUDE_S_MODE;
            trivial_sfence <= |instruction.rs1_addr;
            asid_sfence <= |instruction.rs2_addr;
            is_mret <= (instruction.upper_opcode == SYSTEM_T) & (instruction[31:20] == MRET_imm) & CONFIG.INCLUDE_M_MODE;
            is_sret <= (instruction.upper_opcode == SYSTEM_T) & (instruction[31:20] inside {SRET_imm}) & CONFIG.INCLUDE_S_MODE;
            is_wfi <= (instruction.upper_opcode == SYSTEM_T) & (instruction[31:20] == WFI_imm) & CONFIG.INCLUDE_M_MODE;
        end
    end

    ////////////////////////////////////////////////////
    //Issue
    logic is_ifence_r;
    logic is_sfence_r;
    logic is_mret_r;
    logic is_sret_r;
    logic [31:0] pc_p4_r;
    logic trivial_sfence_r;
    logic asid_sfence_r;
    logic [31:0] sfence_addr_r;
    logic [ASIDLEN-1:0] asid_r;

    //Input registering
    always_ff @(posedge clk) begin
        if (rst) begin
            is_ifence_r <= 0;
            is_sfence_r <= 0;
            is_mret_r <= 0;
            is_sret_r <= 0;
        end
        else begin
            is_ifence_r <= (is_ifence_r & ~(next_state == IDLE_STATE)) | (issue.new_request & is_ifence);
            is_sfence_r <= (is_sfence_r & ~(next_state == IDLE_STATE)) | (issue.new_request & is_sfence);
            is_mret_r <= (is_mret_r & ~(next_state == IDLE_STATE)) | (issue.new_request & is_mret);
            is_sret_r <= (is_sret_r & ~(next_state == IDLE_STATE)) | (issue.new_request & is_sret);
        end  
    end

    always_ff @(posedge clk) begin
        if (instruction_issued)
            pc_p4_r <= constant_alu; //Next instruction for IFENCE, SFENCE, CSR flush
        if (issue.new_request) begin
            trivial_sfence_r <= trivial_sfence;
            asid_sfence_r <= asid_sfence;
            sfence_addr_r <= rf[RS1];
            asid_r <= rf[RS2][ASIDLEN-1:0];
        end
    end

    ////////////////////////////////////////////////////
    //GC Operation
    assign gc.fetch_flush = branch_flush | gc_pc_override;

    always_ff @ (posedge clk) begin
        gc_fetch_hold <= next_state inside {PRE_CLEAR_STATE, INIT_CLEAR_STATE, PRE_ISSUE_FLUSH, TLB_CLEAR_STATE, WAIT_WRITE};
        gc_issue_hold <= next_state inside {PRE_CLEAR_STATE, INIT_CLEAR_STATE, WAIT_INTERRUPT, PRE_ISSUE_FLUSH, TLB_CLEAR_STATE, WAIT_WRITE};
        gc_init_clear <= next_state inside {INIT_CLEAR_STATE};
        gc_fetch_ifence <= issue.new_request & is_ifence;
        gc_tlb_flush <= next_state inside {INIT_CLEAR_STATE, TLB_CLEAR_STATE};
    end
    //work-around for verilator BLKANDNBLK signal optimizations
    assign gc.fetch_hold = gc_fetch_hold;
    assign gc.issue_hold = gc_issue_hold | possible_exception;
    assign gc.init_clear = gc_init_clear;
    assign gc.fetch_ifence = CONFIG.INCLUDE_IFENCE & gc_fetch_ifence;
    assign gc.sfence = '{
        valid : CONFIG.INCLUDE_S_MODE & gc_tlb_flush,
        asid_only : asid_sfence_r,
        asid : asid_r,
        addr_only : trivial_sfence_r,
        addr : sfence_addr_r
    };

    ////////////////////////////////////////////////////
    //GC State Machine
    always @(posedge clk) begin
        if (rst)
            state <= RST_STATE;
        else
            state <= next_state;
    end

    always_comb begin
        next_state = state;
        case (state)
            RST_STATE : next_state = PRE_CLEAR_STATE;
            PRE_CLEAR_STATE : next_state = INIT_CLEAR_STATE;
            INIT_CLEAR_STATE : if (init_clear_done) next_state = IDLE_STATE;
            IDLE_STATE : begin
                if ((issue.new_request & ~is_wfi) | gc.exception.valid | csr_frontend_flush)
                    next_state = PRE_ISSUE_FLUSH;
                else if (interrupt_pending)
                    next_state = WAIT_INTERRUPT;
            end
            WAIT_INTERRUPT : begin
                if (gc.exception.valid | csr_frontend_flush) //Exception overrides interrupt
                    next_state = PRE_ISSUE_FLUSH;
                else if (~interrupt_pending) //An issued CSR instruction cancelled the interrupt
                    next_state = IDLE_STATE;
                else if (~possible_exception & issue_stage.stage_valid & ~branch_flush) //No more possible exceptions and issue stage has correct PC
                    next_state = PRE_ISSUE_FLUSH;
            end
            PRE_ISSUE_FLUSH : begin
                if (is_sfence_r)
                    next_state = TLB_CLEAR_STATE;
                else if (is_ifence_r)
                    next_state = WAIT_WRITE;
                else //MRET/SRET, exception, interrupt, CSR flush
                    next_state = IDLE_STATE;
            end
            //gc.exception will never be set in these states
            TLB_CLEAR_STATE : if (tlb_clear_done) next_state = (load_store_status.outstanding_store) ? WAIT_WRITE : IDLE_STATE;
            WAIT_WRITE : if (~load_store_status.outstanding_store) next_state = IDLE_STATE;
            default : next_state = RST_STATE;
        endcase
    end

    //Will never encounter an exception and can ignore interrupts -> will not have a new instruction on the transition to idle; interrupts can be ignored
    //SFENCE: PRE_ISSUE_FLUSH (Override PC) -> TLB_CLEAR -> WAIT_WRITE
    //IFENCE: PRE_ISSUE_FLUSH (Override PC) -> WAIT_WRITE
    //MRET/SRET: PRE_ISSUE_FLUSH (Override PC)

    //Branch/CSR/LS exceptions: PRE_ISSUE_FLUSH (Override PC)
    //Fetch/illegal exception: PRE_ISSUE_FLUSH (Override PC)

    //Interrupt: WAIT_UNTIL_RETIRED (capture next PC) -> PRE_ISSUE_FLUSH (Override PC) <- This can be hijacked by an exception

    //Interrupt
    //wait until issue/execute exceptions are no longer possible, flush fetch, take exception

    ////////////////////////////////////////////////////
    //State Counter
    logic [$clog2(INIT_CLEAR_DEPTH):0] state_counter;
    always_ff @ (posedge clk) begin
        if (rst | next_state inside {IDLE_STATE})
            state_counter <= 0;
        else if (next_state inside {INIT_CLEAR_STATE, TLB_CLEAR_STATE})
            state_counter <= state_counter + 1;
    end
    assign init_clear_done = state_counter[$clog2(INIT_CLEAR_DEPTH)];
    assign tlb_clear_done = state_counter[$clog2(TLB_CLEAR_DEPTH)] | trivial_sfence_r;

    ////////////////////////////////////////////////////
    //Exception handling
    logic [NUM_EXCEPTION_SOURCES-1:0] exception_valid;
    logic [NUM_EXCEPTION_SOURCES-1:0] exception_possible;

    //Separated out because possible exceptions from CSR must still stall even without M
    generate for (genvar i = 0; i < NUM_EXCEPTION_SOURCES; i++) begin : gen_possible_exceptions
        assign exception_possible[i] = exception[i].possible;
    end endgenerate
    assign possible_exception = |exception_possible;

    generate if (CONFIG.INCLUDE_M_MODE) begin :gen_gc_m_mode

    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    exception_code_t [NUM_EXCEPTION_SOURCES-1:0] exception_code;
    logic [NUM_EXCEPTION_SOURCES-1:0][31:0] exception_tval;
    logic [NUM_EXCEPTION_SOURCES-1:0][31:0] exception_pc;
    exception_sources_t current_exception_unit;
    
    for (genvar i = 0; i < NUM_EXCEPTION_SOURCES; i++) begin
        assign exception_valid[i] = exception[i].valid;
        
        assign exception_code[i] = exception[i].code;
        assign exception_tval[i] = exception[i].tval;
        assign exception_pc[i] = exception[i].pc;
    end
    
    one_hot_to_integer #(.C_WIDTH(NUM_EXCEPTION_SOURCES)) ex_enc (
        .one_hot (exception_valid),
        .int_out (current_exception_unit)
    );

    always_comb begin
        gc.exception.valid = |exception_valid;
        gc.exception.pc = gc.exception.valid ? exception_pc[current_exception_unit] : issue_stage.pc;
        gc.exception.code = exception_code[current_exception_unit];
        gc.exception.tval = exception_tval[current_exception_unit];
    end

    assign interrupt_taken = interrupt_pending & (next_state == PRE_ISSUE_FLUSH) & ~(gc.exception.valid) & ~csr_frontend_flush;

    assign mret = is_mret_r;
    assign sret = is_sret_r;

    end endgenerate

    //PC determination (trap, flush or return)
    //Two cycles: on first cycle the processor front end is flushed,
    //on the second cycle the new PC is fetched
    generate if (CONFIG.INCLUDE_M_MODE || CONFIG.INCLUDE_IFENCE) begin :gen_gc_pc_override

    always_ff @ (posedge clk) begin
        gc_pc_override <= next_state inside {PRE_ISSUE_FLUSH, INIT_CLEAR_STATE};
        gc_pc <=
                        (gc.exception.valid | interrupt_taken) ? exception_target_pc :
                        (is_ifence_r | is_sfence_r | csr_frontend_flush) ? pc_p4_r :
                        epc; //ret
    end
    //work-around for verilator BLKANDNBLK signal optimizations
    assign gc.pc_override = gc_pc_override;
    assign gc.pc = gc_pc;

    end endgenerate
    ////////////////////////////////////////////////////
    //Decode / Write-back Handshaking
    //CSR reads are passed through the Load-Store unit
    //A CSR write is only committed once it is the oldest instruction in the pipeline
    //while processing a csr operation, gc_issue_hold prevents further instructions from being issued
    assign issue.ready = 1;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    multiple_exceptions_assertion:
        assert property (@(posedge clk) disable iff (rst) $onehot0(exception_valid))
        else $error("Simultaneous exceptions");

    multiple_possible_exceptions_assertion:
        assert property (@(posedge clk) disable iff (rst) $onehot0(exception_possible))
        else $error("Simultaneous possible exceptions");

endmodule
