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

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,

        //Decode
        unit_issue_interface.unit issue,
        input gc_inputs_t gc_inputs,

        //Branch miss predict
        input logic branch_flush,

        //exception_interface.unit pre_issue_exception,

        //Exception
        exception_interface.econtrol exception [NUM_EXCEPTION_SOURCES],
        input logic [31:0] exception_target_pc,
        input logic [31:0] oldest_pc,

        output logic mret,
        output logic sret,
        input logic [31:0] epc,

        //Retire
        input retire_packet_t retire,
        input id_t retire_ids [RETIRE_PORTS],
        input id_t retire_ids_next [RETIRE_PORTS],
        input logic [$clog2(NUM_EXCEPTION_SOURCES)-1:0] current_exception_unit,

        //CSR Interrupts
        input logic interrupt_pending,
        output logic interrupt_taken,

        input logic processing_csr,

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

    typedef enum {RST_STATE, PRE_CLEAR_STATE, INIT_CLEAR_STATE, IDLE_STATE, TLB_CLEAR_STATE, POST_ISSUE_DRAIN, PRE_ISSUE_FLUSH, POST_ISSUE_DISCARD} gc_state;
    gc_state state;
    gc_state next_state;

    logic init_clear_done;
    logic tlb_clear_done;

    gc_inputs_t gc_inputs_r;
    logic post_issue_idle;
    logic ifence_in_progress;
    logic ret_in_progress;

    //GC registered global outputs
    logic gc_init_clear;
    logic gc_fetch_hold;
    logic gc_issue_hold;
    logic gc_fetch_flush;
    logic gc_writeback_supress;
    logic gc_retire_hold;
    logic gc_tlb_flush;
    logic gc_sq_flush;
    logic gc_pc_override;
    logic [31:0] gc_pc;

    ////////////////////////////////////////////////////
    //Implementation
    //Input registering
    always_ff @(posedge clk) begin
        if (issue.new_request)
            gc_inputs_r <= gc_inputs;
    end

    //ret
    always_ff @(posedge clk) begin
        if (rst)
            ret_in_progress <= 0;
        else
            ret_in_progress <= (ret_in_progress & ~(next_state == PRE_ISSUE_FLUSH)) | (issue.new_request & (gc_inputs.is_mret | gc_inputs.is_sret));
    end

    //ifence
    always_ff @(posedge clk) begin
        if (rst)
            ifence_in_progress <= 0;
        else
            ifence_in_progress <= (ifence_in_progress & ~(next_state == PRE_ISSUE_FLUSH)) | (issue.new_request & gc_inputs.is_ifence);
    end

    ////////////////////////////////////////////////////
    //GC Operation
    assign post_issue_idle = (post_issue_count == 0) & load_store_status.sq_empty;
    assign gc.fetch_flush = branch_flush | gc_pc_override;

    always_ff @ (posedge clk) begin
        gc_fetch_hold <= next_state inside {PRE_CLEAR_STATE, INIT_CLEAR_STATE, POST_ISSUE_DRAIN, PRE_ISSUE_FLUSH};
        gc_issue_hold <= processing_csr | (next_state inside {PRE_CLEAR_STATE, INIT_CLEAR_STATE, TLB_CLEAR_STATE, POST_ISSUE_DRAIN, PRE_ISSUE_FLUSH, POST_ISSUE_DISCARD});
        gc_writeback_supress <= next_state inside {PRE_CLEAR_STATE, INIT_CLEAR_STATE, POST_ISSUE_DISCARD};
        gc_retire_hold <= next_state inside {PRE_ISSUE_FLUSH};
        gc_init_clear <= next_state inside {INIT_CLEAR_STATE};
        gc_tlb_flush <= next_state inside {INIT_CLEAR_STATE, TLB_CLEAR_STATE};
        gc_sq_flush <= state inside {POST_ISSUE_DISCARD} & next_state inside {IDLE_STATE};
    end
    //work-around for verilator BLKANDNBLK signal optimizations
    assign gc.fetch_hold = gc_fetch_hold;
    assign gc.issue_hold = gc_issue_hold;
    assign gc.writeback_supress = CONFIG.INCLUDE_M_MODE & gc_writeback_supress;
    assign gc.retire_hold = gc_retire_hold;
    assign gc.init_clear = gc_init_clear;
    assign gc.tlb_flush = CONFIG.INCLUDE_S_MODE & gc_tlb_flush;
    assign gc.sq_flush = CONFIG.INCLUDE_M_MODE & gc_sq_flush;
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
                if (gc.exception.valid)//new pending exception is also oldest instruction
                    next_state = PRE_ISSUE_FLUSH;
                else if (issue.new_request | interrupt_pending | gc.exception_pending)
                    next_state = POST_ISSUE_DRAIN;
            end
            TLB_CLEAR_STATE : if (tlb_clear_done) next_state = IDLE_STATE;
            POST_ISSUE_DRAIN : if (((ifence_in_progress | ret_in_progress) & post_issue_idle) | gc.exception.valid | interrupt_pending) next_state = PRE_ISSUE_FLUSH;
            PRE_ISSUE_FLUSH : next_state = POST_ISSUE_DISCARD;
            POST_ISSUE_DISCARD : if ((post_issue_count == 0) & load_store_status.no_released_stores_pending) next_state = IDLE_STATE;
            default : next_state = RST_STATE;
        endcase
    end

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
    assign tlb_clear_done = state_counter[$clog2(TLB_CLEAR_DEPTH)];

    ////////////////////////////////////////////////////
    //Exception handling
    generate if (CONFIG.INCLUDE_M_MODE) begin :gen_gc_m_mode

    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    logic [NUM_EXCEPTION_SOURCES-1:0] exception_pending;
    exception_code_t [NUM_EXCEPTION_SOURCES-1:0] exception_code;
    id_t [NUM_EXCEPTION_SOURCES-1:0] exception_id;
    logic [NUM_EXCEPTION_SOURCES-1:0][31:0] exception_tval;
    logic exception_ack;
    
    for (genvar i = 0; i < NUM_EXCEPTION_SOURCES; i++) begin
        assign exception_pending[i] = exception[i].valid;
        assign exception_code[i] = exception[i].code;
        assign exception_id[i] = exception[i].id;
        assign exception_tval[i] = exception[i].tval;
        assign exception[i].ack = exception_ack;
    end
    
    //Exception valid when the oldest instruction is a valid ID.  This is done with a level of indirection (through the exception unit table)
    //for better scalability, avoiding the need to compare against all exception sources.
    always_comb begin
        gc.exception_pending = |exception_pending;
        gc.exception.valid = (retire_ids_next[0] == exception_id[current_exception_unit]) & exception_pending[current_exception_unit];
        gc.exception.pc = oldest_pc;
        gc.exception.code = exception_code[current_exception_unit];
        gc.exception.tval = exception_tval[current_exception_unit];
    end

    assign exception_ack = gc.exception.valid;

    assign interrupt_taken = interrupt_pending & (next_state == PRE_ISSUE_FLUSH) & ~(ifence_in_progress | ret_in_progress | gc.exception.valid);

    assign mret = gc_inputs_r.is_mret & ret_in_progress & (next_state == PRE_ISSUE_FLUSH);
    assign sret = gc_inputs_r.is_sret & ret_in_progress & (next_state == PRE_ISSUE_FLUSH);

    end endgenerate

    //PC determination (trap, flush or return)
    //Two cycles: on first cycle the processor front end is flushed,
    //on the second cycle the new PC is fetched
    generate if (CONFIG.INCLUDE_M_MODE || CONFIG.INCLUDE_IFENCE) begin :gen_gc_pc_override

    always_ff @ (posedge clk) begin
        gc_pc_override <= next_state inside {PRE_ISSUE_FLUSH, INIT_CLEAR_STATE};
        gc_pc <=
                        (gc.exception.valid | interrupt_taken) ? exception_target_pc :
                        (gc_inputs_r.is_ifence) ? gc_inputs_r.pc_p4 :
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
    `ifdef ENABLE_SIMULATION_ASSERTIONS
    generate if (DEBUG_CONVERT_EXCEPTIONS_INTO_ASSERTIONS) begin
        unexpected_exception_assertion:
            assert property (@(posedge clk) disable iff (rst) (~gc.exception.valid))
            else $error("unexpected exception occured: %s", gc.exception.code.name());
    end endgenerate
    `endif

endmodule
