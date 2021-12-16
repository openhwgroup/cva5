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

    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
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
        input logic gc_flush_required,
        //Branch miss predict
        input logic branch_flush,

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
        input logic [$clog2(NUM_EXCEPTION_SOURCES)-1:0] current_exception_unit,

        //CSR Interrupts
        input logic interrupt_pending,
        output logic interrupt_taken,

        //Output controls
        output gc_outputs_t gc,

        //Ordering support
        input logic sq_empty,
        input logic [LOG2_MAX_IDS:0] post_issue_count
    );

    //Largest depth for TLBs
    localparam int TLB_CLEAR_DEPTH = (CONFIG.DTLB.DEPTH > CONFIG.ITLB.DEPTH) ? CONFIG.DTLB.DEPTH : CONFIG.ITLB.DEPTH;
    //For general reset clear, greater of TLB depth or id-flight memory blocks (MAX_IDS)
    localparam int INIT_CLEAR_DEPTH = CONFIG.INCLUDE_S_MODE ? (TLB_CLEAR_DEPTH > 64 ? TLB_CLEAR_DEPTH : 64) : 64;

    ////////////////////////////////////////////////////
    //Instructions
    //All instructions are processed only if in IDLE state, meaning there can be no exceptions caused by instructions already further in the pipeline.
    //FENCE:
    //    Drain Load/Store FIFO
    //FENCE.I:
    //    flush and hold fetch until L/S unit empty
    //    Local mem (nothing extra required for coherency)
    //    Caches, currently not supported.  Need snooping for Icache and draining of data FIFO to L2 and after FIFO drained, poping at least the current number of entries in the invalidation FIFO
    //SFENCE
    //    flush and hold fetch, wait until L/S input FIFO empty, hold fetch until TLB update complete
    //ECALL, EBREAK, SRET, MRET:
    //    flush fetch, update to CSRs is pipelined

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

    typedef enum {RST_STATE, PRE_CLEAR_STATE, INIT_CLEAR_STATE, IDLE_STATE, HOLD_STATE, TLB_CLEAR_STATE, IQ_DRAIN} gc_state;
    gc_state state;
    gc_state next_state;

    logic init_clear_done;
    logic tlb_clear_done;

    logic i_fence_flush;
    exception_code_t ecall_code;
    logic second_cycle_flush;

    logic system_op_or_exception_complete;
    logic exception_with_rd_complete;

    logic [1:0] current_privilege;

    gc_inputs_t stage1;

    logic post_issue_idle;
    //CSR
    logic processing_csr;

    //GC registered global outputs
    logic gc_init_clear;
    logic gc_fetch_hold;
    logic gc_issue_hold;
    logic gc_issue_flush;
    logic gc_fetch_flush;
    logic gc_supress_writeback;
    logic gc_tlb_flush;
    logic gc_pc_override;
    logic [31:0] gc_pc;

    ////////////////////////////////////////////////////
    //Implementation
    //Input registering
    always_ff @(posedge clk) begin
        if (issue.possible_issue & ~gc.issue_hold) begin
            stage1 <= gc_inputs;
        end
    end


    ////////////////////////////////////////////////////
    //GC Operation
    assign post_issue_idle = (post_issue_count == 0) & sq_empty;
    assign gc.fetch_flush = branch_flush | gc_pc_override;

    always_ff @ (posedge clk) begin
        gc_fetch_hold <=  next_state inside {PRE_CLEAR_STATE, INIT_CLEAR_STATE};
        gc_issue_hold <= issue.new_request | processing_csr | (next_state inside {PRE_CLEAR_STATE, INIT_CLEAR_STATE, HOLD_STATE, TLB_CLEAR_STATE, IQ_DRAIN});
        gc_supress_writeback <= next_state inside {PRE_CLEAR_STATE, INIT_CLEAR_STATE, TLB_CLEAR_STATE};
        gc_init_clear <= next_state inside {INIT_CLEAR_STATE};
        gc_tlb_flush <= next_state inside {INIT_CLEAR_STATE, TLB_CLEAR_STATE};
    end
    //work-around for verilator BLKANDNBLK signal optimizations
    assign gc.fetch_hold = gc_fetch_hold;
    assign gc.issue_hold = gc_issue_hold;
    assign gc.supress_writeback = gc_supress_writeback;
    assign gc.init_clear = gc_init_clear;
    assign gc.tlb_flush = gc_tlb_flush;
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
                if (issue.new_request)
                    next_state = HOLD_STATE;
                //IF exception and post-issue > 1 OR FLUSHING interrupts
                //if (ls_exception.valid | potential_branch_exception | system_op_or_exception_complete) begin
                //    next_state = IQ_DRAIN;
                //end
            end
            HOLD_STATE : if (post_issue_idle) next_state = IDLE_STATE;
            TLB_CLEAR_STATE : if (tlb_clear_done) next_state = IDLE_STATE;
            IQ_DRAIN : if (post_issue_idle) next_state = IDLE_STATE;
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
    //mret/sret
    always_ff @ (posedge clk) begin
        mret = issue.new_request & gc_inputs.is_ret & (gc_inputs.instruction[31:25] == 7'b0011000);
        sret = issue.new_request & gc_inputs.is_ret & (gc_inputs.instruction[31:25] == 7'b0001000);
    end
    ////////////////////////////////////////////////////
    //Exception handling

    //The type of call instruction is depedent on the current privilege level
    always_comb begin
        case (current_privilege)
            USER_PRIVILEGE : ecall_code = ECALL_U;
            SUPERVISOR_PRIVILEGE : ecall_code = ECALL_S;
            MACHINE_PRIVILEGE : ecall_code = ECALL_M;
            default : ecall_code = ECALL_U;
        endcase
    end

    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    logic [NUM_EXCEPTION_SOURCES-1:0] ex_pending;
    exception_code_t [NUM_EXCEPTION_SOURCES-1:0] ex_code;
    id_t [NUM_EXCEPTION_SOURCES-1:0] ex_id;
    logic [NUM_EXCEPTION_SOURCES-1:0][31:0] ex_tval;
    logic ex_ack;
    generate
        for (genvar i = 0; i < NUM_EXCEPTION_SOURCES; i++) begin
            assign ex_pending[i] = exception[i].valid;
            assign ex_code[i] = exception[i].code;
            assign ex_id[i] = exception[i].id;
            assign ex_tval[i] = exception[i].tval;
            assign exception[i].ack = ex_ack;
        end
    endgenerate
    
    //Exception valid when the oldest instruction is a valid ID.  This is done with a level of indirection (through the exception unit table)
    //for better scalability, avoiding the need to compare against all exception sources.
    always_comb begin
        gc.exception_pending = |ex_pending;
        gc.exception.valid = (retire_ids[0] == ex_id[current_exception_unit]) & ex_pending[current_exception_unit];
        gc.exception.pc = oldest_pc;
        gc.exception.code = ex_code[current_exception_unit];
        gc.exception.tval = ex_tval[current_exception_unit];
    end

    always_ff @ (posedge clk) begin
        ex_ack <= gc.exception.valid;
    end

    //PC determination (trap, flush or return)
    //Two cycles: on first cycle the processor front end is flushed,
    //on the second cycle the new PC is fetched
    always_ff @ (posedge clk) begin
        second_cycle_flush <= gc_flush_required;
        gc_pc_override <= gc_flush_required | second_cycle_flush | gc.exception.valid | (next_state == INIT_CLEAR_STATE);
        gc_pc <=
                        gc.exception.valid ? exception_target_pc :
                        gc_inputs.is_ret ? epc :
                        stage1.pc_p4; //ifence
    end
    //work-around for verilator BLKANDNBLK signal optimizations
    assign gc.pc_override = gc_pc_override;
    assign gc.pc = gc_pc;

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
