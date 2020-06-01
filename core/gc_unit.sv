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
import riscv_types::*;
import taiga_types::*;
import csr_types::*;

module gc_unit(
        input logic clk,
        input logic rst,


        //Decode
        unit_issue_interface.unit issue,
        input gc_inputs_t gc_inputs,
        input logic instruction_issued_no_rd,
        input logic gc_flush_required,
        //Branch miss predict
        input logic branch_flush,
        //instruction misalignement
        input logic potential_branch_exception,
        input exception_packet_t br_exception,
        input logic branch_exception_is_jump,
        //Illegal instruction
        input logic illegal_instruction,

        //Load Store Unit
        input exception_packet_t ls_exception,

        //TLBs
        output logic tlb_on,
        output logic [ASIDLEN-1:0] asid,

        //MMUs
        mmu_interface.csr immu,
        mmu_interface.csr dmmu,

        //ID Management
        output logic system_op_or_exception_complete,
        output id_t system_op_or_exception_id,

        //Exception
        output id_t exception_id,
        input logic [31:0] exception_pc,

        //WB
        input logic instruction_retired,
        input logic instruction_queue_empty,
        input logic writeback_is_idle,
        //unit_writeback_interface.unit gc_wb,

        //External
        input logic interrupt,
        input logic timer_interrupt,

        //Output controls
        output logic gc_issue_hold,
        output logic gc_issue_flush,
        output logic gc_fetch_flush,
        output logic gc_fetch_pc_override,
        output logic gc_supress_writeback,

        output logic [31:0] gc_fetch_pc,

        //Write-back to Load-Store Unit
        output logic[31:0] csr_rd,
        output id_t csr_id,
        output logic csr_done,
        input logic ls_is_idle
        );

    //Largest depth for TLBs
    localparam int TLB_CLEAR_DEPTH = (DTLB_DEPTH > ITLB_DEPTH) ? DTLB_DEPTH : ITLB_DEPTH;
    //For general reset clear, greater of TLB depth or inuse memory block (32-bits)
    localparam int CLEAR_DEPTH = ENABLE_S_MODE ? TLB_CLEAR_DEPTH : 32;

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

    typedef enum {RST_STATE, IDLE_STATE, TLB_CLEAR_STATE, IQ_DRAIN} gc_state;
    gc_state state;
    gc_state next_state;
    gc_state prev_state;

    logic tlb_clear_done;

    logic i_fence_flush;
    exception_code_t ecall_code;
    logic second_cycle_flush;

    //CSR
    logic mret;
    logic sret;
    logic [XLEN-1:0] wb_csr;
    csr_inputs_t csr_inputs;
    exception_packet_t gc_exception;
    exception_packet_t csr_exception;
    logic [1:0] current_privilege;
    logic [31:0] trap_pc;
    logic [31:0] csr_mepc;
    logic [31:0] csr_sepc;

    //Write-back handshaking
    logic [2:0] fn3;
    logic [6:0] opcode;
    logic [4:0] opcode_trim;

    logic [4:0] rs1_addr;
    logic [4:0] rs2_addr;
    logic [4:0] rd_addr;

    gc_inputs_t stage1;
    logic processing_csr;
    logic csr_ready_to_complete;
    logic csr_ready_to_complete_r;
    id_t instruction_id;

    //implementation
    ////////////////////////////////////////////////////
    always_ff @(posedge clk) begin
        if (issue.possible_issue) begin
            stage1 <= gc_inputs;
        end
    end

    ////////////////////////////////////////////////////
    //ID Management
    assign system_op_or_exception_complete =
        (issue.new_request & (gc_inputs.is_fence | gc_inputs.is_i_fence)) |
        gc_exception.valid;
    assign system_op_or_exception_id = issue.new_request ? issue.id : exception_id;

    //Instruction decode
    assign opcode = stage1.instruction[6:0];
    assign opcode_trim = opcode[6:2];
    assign fn3 = stage1.instruction[14:12];
    assign rs1_addr = stage1.instruction[19:15];
    assign rd_addr = stage1.instruction[11:7];

    ////////////////////////////////////////////////////
    //GC Operation
    assign gc_fetch_flush = branch_flush | gc_fetch_pc_override;

    always_ff @ (posedge clk) begin
        gc_issue_hold <= issue.new_request || processing_csr || (next_state inside {TLB_CLEAR_STATE, IQ_DRAIN}) || potential_branch_exception;
    end

    always_ff @ (posedge clk) begin
        gc_supress_writeback <= next_state inside {TLB_CLEAR_STATE} ? 1 : 0;
    end

    ////////////////////////////////////////////////////
    //GC State Machine
    always @(posedge clk) begin
        if (rst)
            state <= RST_STATE;
        else
            state <= next_state;
    end

    always @(posedge clk) begin
        if (rst)
            prev_state <= RST_STATE;
        else
            prev_state <= state;
    end

    always_comb begin
        next_state = state;
        case (state)
            RST_STATE : next_state = IDLE_STATE;
            IDLE_STATE : begin
                if (ls_exception.valid | (branch_exception_is_jump & potential_branch_exception)) begin
                    next_state = IQ_DRAIN;
                end
            end
            TLB_CLEAR_STATE : if (tlb_clear_done) next_state = IDLE_STATE;
            IQ_DRAIN : next_state = IDLE_STATE;
            default : next_state = RST_STATE;
        endcase
    end

    //Counters for tlb clearing states
    shift_counter #(.DEPTH(TLB_CLEAR_DEPTH)) tlb_clear_counter (.*, .start((state == IDLE_STATE) && (next_state == TLB_CLEAR_STATE)), .done(tlb_clear_done));

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

    assign exception_id =
        potential_branch_exception ? br_exception.id :
        (ls_exception.valid ? ls_exception.id : issue.id);

    //TODO: check if possible to convert to unique if, verify potential for overlap
    always_comb begin
        //PC sourced from instruction metadata table
        if (br_exception.valid) begin
            gc_exception.code = br_exception.code;
            gc_exception.tval = br_exception.tval;
        end else if (illegal_instruction) begin
            gc_exception.code = ILLEGAL_INST;
            gc_exception.tval = gc_inputs.instruction;//optional, can be zero instead
        end else if (ls_exception.valid) begin
            gc_exception.code = ls_exception.code;
            gc_exception.tval = ls_exception.tval;
        end else if (gc_inputs.is_ecall) begin
            gc_exception.code = ecall_code;
            gc_exception.tval = '0;
        end else begin
            gc_exception.code = BREAK;
            gc_exception.tval = '0;
        end
    end
    logic ecall_break_exception;
    assign ecall_break_exception = issue.new_request & (gc_inputs.is_ecall | gc_inputs.is_ebreak);
    assign gc_exception.valid = ENABLE_M_MODE & (ecall_break_exception | ls_exception.valid | br_exception.valid | illegal_instruction);

    //PC determination (trap, flush or return)
    //Two cycles: on first cycle the processor front end is flushed,
    //on the second cycle the new PC is fetched
    always_ff @ (posedge clk) begin
        second_cycle_flush <= gc_flush_required;
        gc_fetch_pc_override <= gc_flush_required | second_cycle_flush | ls_exception.valid | br_exception.valid;
        if (gc_exception.valid | stage1.is_i_fence | (issue.new_request & gc_inputs.is_ret)) begin
            gc_fetch_pc <= gc_exception.valid ? trap_pc :
                stage1.is_i_fence ? stage1.pc + 4 : //Could stall on dec_pc valid and use instead of another adder
                csr_mepc;// gc_inputs.is_ret
        end
    end

    ////////////////////////////////////////////////////
    //CSR registers
    assign csr_inputs.rs1 = fn3[2] ? {27'b0, rs1_addr} : stage1.rs1;
    assign csr_inputs.csr_addr = stage1.instruction[31:20];
    assign csr_inputs.csr_op = fn3[1:0];
    assign csr_inputs.rs1_is_zero = (rs1_addr == 0);
    assign csr_inputs.rd_is_zero = (rd_addr == 0);

    csr_regs csr_registers (.*, .new_request(stage1.is_csr), .read_regs(csr_ready_to_complete), .commit(csr_ready_to_complete_r));

    ////////////////////////////////////////////////////
    //Decode / Write-back Handshaking
    //CSR reads are passed through the Load-Store unit
    //A CSR write is only committed once it is the oldest instruction in the pipeline
    //while processing a csr operation, gc_issue_hold prevents further instructions from being issued
    assign issue.ready = 1;

    set_clr_reg_with_rst #(.SET_OVER_CLR(0), .WIDTH(1), .RST_VALUE(0)) processing_csr_m (
      .clk, .rst,
      .set(issue.new_request & gc_inputs.is_csr),
      .clr(csr_ready_to_complete),
      .result(processing_csr)
    );

    assign csr_ready_to_complete = processing_csr & ls_is_idle & writeback_is_idle;
    always_ff @(posedge clk) begin
        csr_ready_to_complete_r <= csr_ready_to_complete;
        csr_id <= instruction_id;
        if (issue.new_request) begin
            instruction_id <= issue.id;
        end
    end

    assign csr_done = csr_ready_to_complete_r;
    assign csr_rd = wb_csr;

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////

endmodule
