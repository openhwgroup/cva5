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

import taiga_config::*;
import taiga_types::*;

module gc_unit(
        input logic clk,
        input logic rst,
        input logic interrupt,

        func_unit_ex_interface.unit gc_ex,
        input gc_inputs_t gc_inputs,

        input instruction_id_t oldest_id,
        input logic inflight_queue_empty,

        exception_interface.econtrol ls_exception,
        input logic load_store_issue,
        input logic load_store_FIFO_emptying,

        exception_interface.econtrol csr_exception,
        output logic mret,
        output logic sret,
        output logic ecall,
        output logic ebreak,

        csr_exception_interface.econtrol gc_exception,

        output logic gc_issue_hold,
        output logic gc_issue_flush,
        output logic gc_fetch_hold,
        output logic gc_fetch_flush,
        output logic gc_supress_writeback,

        output logic inorder,
        output logic inuse_clear
        );

    //Largest depth for TLBs
    localparam int TLB_CLEAR_DEPTH = (DTLB_DEPTH > ITLB_DEPTH) ? DTLB_DEPTH : ITLB_DEPTH;
    //For general reset clear, greater of TLB depth or inuse memory block (32-bits)
    localparam int CLEAR_DEPTH = USE_MMU ? TLB_CLEAR_DEPTH : 32;

    logic [CLEAR_DEPTH-1:0] clear_shift_count;
    logic [TLB_CLEAR_DEPTH-1:0] tlb_clear_shift_count;
    ////////////////////////////////////////////////////
    enum {OP_ECALL, OP_EBREAK, OP_SRET, OP_MRET, OP_SFENCE, OP_FENCE, OP_FENCEI} operation;

    //Instructions
    //All instructions are processed only if in IDLE state, meaning there can be no exceptions caused by instructions already further in the pipeline.
    //FENCE:
    //    Drain Load/Store FIFO (i.e. not in in-order mode)
    //FENCE.I:
    //    flush and hold fetch until L/S unit empty
    //SFENCE
    //    flush and hold fetch, wait until L/S input FIFO empty, hold fetch until TLB update complete
    //ECALL, EBREAK, SRET, MRET:
    //    flush fetch, update CSRs (could be illegal instruction exception as well)

    //Interrupt
    //Hold issue, wait until IDLE state, flush fetch, take exception

    //Fetch Exception
    //flush fetch, wait until IDLE state, take exception.  If decode stage or later exception occurs first, exception is overridden

    //Illegal opcode (decode stage)
    //fetch flush, issue hold, wait until IDLE state, take exception.  If execute or later exception occurs first, exception is overridden

    //CSR exceptions
    //fetch flush, issue hold, capture ID/rd_non_zero and drain instruction queue, take exception.

    //LS exceptions (miss-aligned, TLB and MMU)
    //fetch flush, issue hold, capture ID/rd_non_zero and drain instruction queue, take exception.

    //Instruction queue drain:
    //  Two possibilities:
    //      1. Instruction stores to reg file.  ID in instruction queue, wait until that ID is oldest (either find oldest valid, or for small cycle penalty just look at last entry and wait for ID and valid)
    //      2. Instruction does not store to reg file.  If IQ not empty, wait for previously issued ID to complete, if empty no waiting required.
    //
    //      After all preceding instructions have been committed, continue popping instructions from queue but supress write-back operation until queue is drained.

    //In-order mode:
    //  Turn on when an instruction in the execute phase could cause an interrupt (L/S or CSR)
    //  Turn off when exception can no-longer occur (after one cycle for CSR, when L/S input FIFO will be empty)

    //*Complete issued instructions before exception
    //*Drain L/S FIFO then Hold fetch/issue during TLB clear
    //*Hold fetch until all stores committed
    //*Turn on inorder mode when L/S issued, turn off when no instruction can cause interrupt
    //     *If in-order mode and inflight queue empty, disable zero cycle write-back (eg. ALU)
    //*Hold fetch during potential fetch exception, when fetch buffer drained, if no other exceptions trigger exception

    typedef enum {RST_STATE, PRE_CLEAR_STATE, CLEAR_STATE, IDLE_STATE, TLB_CLEAR_STATE, LS_EXCEPTION_POSSIBLE, IQ_DRAIN} gc_state;
    gc_state state;
    gc_state next_state;

    //implementation
    ////////////////////////////////////////////////////
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
            PRE_CLEAR_STATE : next_state = CLEAR_STATE;
            CLEAR_STATE : if (clear_shift_count[CLEAR_DEPTH-1]) next_state = IDLE_STATE;
            IDLE_STATE : if (load_store_issue) next_state = LS_EXCEPTION_POSSIBLE;
            TLB_CLEAR_STATE : if (tlb_clear_shift_count[TLB_CLEAR_DEPTH-1]) next_state = IDLE_STATE;
            LS_EXCEPTION_POSSIBLE : if (load_store_FIFO_emptying) next_state = IDLE_STATE;
            default : next_state = RST_STATE;
        endcase
    end

    always_ff @ (posedge clk) begin
        gc_issue_hold <=  (next_state inside {PRE_CLEAR_STATE, CLEAR_STATE, TLB_CLEAR_STATE}) ? 1 : 0;
        inuse_clear <= (next_state inside {CLEAR_STATE}) ? 1 : 0;
        inorder <= (next_state inside {LS_EXCEPTION_POSSIBLE, IQ_DRAIN}) ? 1 : 0;
    end

    assign gc_issue_flush = 0;
    assign gc_fetch_hold = 0;
    assign gc_fetch_flush = 0;
    assign gc_supress_writeback = 0;

    //CLEAR state shift reg
    always_ff @ (posedge clk) begin
        clear_shift_count[0] <= (state == PRE_CLEAR_STATE) && (next_state == CLEAR_STATE);
        clear_shift_count[CLEAR_DEPTH-1:1] <= clear_shift_count[CLEAR_DEPTH-2:0];
    end
    //TLB_CLEAR state shift reg
    always_ff @ (posedge clk) begin
        tlb_clear_shift_count[0] <= (state == IDLE_STATE) && (next_state == TLB_CLEAR_STATE);
        tlb_clear_shift_count[TLB_CLEAR_DEPTH-1:1] <= tlb_clear_shift_count[TLB_CLEAR_DEPTH-2:0];
    end


    ////////////////////////////////////////////////////
    assign gc_ex.ready = 1;


    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert ((gc_ex.new_request && state == IDLE_STATE) || !gc_ex.new_request) else $error("Request when not idle.");
    end

    ////////////////////////////////////////////////////

endmodule
