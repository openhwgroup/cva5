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

module mmu

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    import csr_types::*;

    (
        input logic clk,
        input logic rst,
        mmu_interface.mmu mmu,
        input logic abort_request,
        l1_arbiter_request_interface.master l1_request,
        l1_arbiter_return_interface.master l1_response
    );

    typedef struct packed{
        logic [11:0] ppn1;
        logic [9:0] ppn0;
        logic [1:0] reserved;
        logic d;
        logic a;
        logic g;
        logic u;
        logic x;
        logic w;
        logic r;
        logic v;
    } pte_t;

    typedef enum  {
        IDLE = 0,
        SEND_REQUEST_1 = 1,
        WAIT_REQUEST_1 = 2,
        SEND_REQUEST_2 = 3,
        WAIT_REQUEST_2 = 4,
        COMPLETE_SUCCESS = 5,
        COMPLETE_FAULT = 6
    } mmu_state_t;
    logic [6:0] state;
    logic [6:0] next_state;

    pte_t pte;
    logic access_valid;
    logic privilege_valid;

    localparam MAX_ABORTED_REQUESTS = 4;
    logic abort_queue_full;
    logic discard_data;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //L1 arbiter Interfrace
    assign l1_request.rnw = 1;
    assign l1_request.be = '1;
    assign l1_request.size = '0;
    assign l1_request.is_amo = 0;
    assign l1_request.amo = 0;

    assign l1_request.request = (state[SEND_REQUEST_1] | state[SEND_REQUEST_2]) & ~abort_request;

    //Page Table addresses
    always_ff @ (posedge clk) begin
        if (state[IDLE] | l1_response.data_valid) begin
            if (state[IDLE])
                l1_request.addr <= {mmu.satp_ppn[19:0], mmu.virtual_address[31:22], 2'b00};
            else
                l1_request.addr <= {{pte.ppn1[9:0], pte.ppn0}, mmu.virtual_address[21:12], 2'b00};
        end
    end

    assign pte = l1_response.data;

    ////////////////////////////////////////////////////
    //Supports unlimited tracking of aborted requests
    //Assumption: memory requests are returned in-order
    localparam COUNT_W = $clog2(MAX_ABORTED_REQUESTS);
    logic [COUNT_W:0] abort_tracking;
    logic delayed_abort;
    logic delayed_abort_complete;

    assign delayed_abort = abort_request & (state[WAIT_REQUEST_1] | state[WAIT_REQUEST_2]);
    assign delayed_abort_complete = discard_data & l1_response.data_valid;
    always_ff @ (posedge clk) begin
        if (rst)
            abort_tracking <= 0;
        else
            abort_tracking <= abort_tracking - COUNT_W'(delayed_abort) + COUNT_W'(delayed_abort_complete);
    end

    assign discard_data = abort_tracking[COUNT_W];
    assign abort_queue_full = abort_tracking[COUNT_W] & ~|abort_tracking[COUNT_W-1:0];
    ////////////////////////////////////////////////////
    //Access and permission checks
    //A and D bits are software managed
    assign access_valid =
        (mmu.execute & pte.x & pte.a) | //fetch
        (mmu.rnw & (pte.r | (pte.x & mmu.mxr)) & pte.a) | //load
        ((~mmu.rnw & ~mmu.execute) & pte.w & pte.a & pte.d); //store

    assign privilege_valid = 
        (mmu.privilege == MACHINE_PRIVILEGE) |
        ((mmu.privilege == SUPERVISOR_PRIVILEGE) & (~pte.u | (pte.u & mmu.sum))) |
        ((mmu.privilege == USER_PRIVILEGE) & pte.u);

    ////////////////////////////////////////////////////
    //State Machine
    always_comb begin
        next_state = state;
        case (1'b1)
            state[IDLE] :
                if (mmu.request & ~abort_queue_full)
                    next_state = 2**SEND_REQUEST_1;
            state[SEND_REQUEST_1] : 
                if (l1_request.ack)
                    next_state = 2**WAIT_REQUEST_1;
            state[WAIT_REQUEST_1] :
                if (l1_response.data_valid & ~discard_data) begin
                    if (~pte.v | (~pte.r & pte.w)) //page not valid OR invalid xwr pattern
                        next_state = 2**COMPLETE_FAULT;
                    else if (pte.v & (pte.r | pte.x)) begin//superpage (all remaining xwr patterns other than all zeros)
                        if (access_valid & privilege_valid)
                            next_state = 2**COMPLETE_SUCCESS;
                        else
                            next_state = 2**COMPLETE_FAULT;
                    end else //(pte.v & ~pte.x & ~pte.w & ~pte.r) pointer to next level in page table
                        next_state = 2**SEND_REQUEST_2;
                end
            state[SEND_REQUEST_2] : 
                if (l1_request.ack)
                    next_state = 2**WAIT_REQUEST_2;
            state[WAIT_REQUEST_2] : 
                if (l1_response.data_valid & ~discard_data) begin
                    if (access_valid & privilege_valid)
                        next_state = 2**COMPLETE_SUCCESS;
                    else
                        next_state = 2**COMPLETE_FAULT;
                end
            state[COMPLETE_SUCCESS], state[COMPLETE_FAULT]  :
                next_state = 2**IDLE;
        endcase
        //If request is aborted, return to IDLE
        if (abort_request)
            next_state = 2**IDLE;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            state <= 2**IDLE;
        else
            state <= next_state;
    end

    ////////////////////////////////////////////////////
    //TLB return path
    always_ff @ (posedge clk) begin
        if (l1_response.data_valid) begin
            mmu.upper_physical_address[19:10] <= pte.ppn1[9:0];
            mmu.upper_physical_address[9:0] <= state[WAIT_REQUEST_2] ? pte.ppn0 : mmu.virtual_address[21:12];
        end
    end
    assign mmu.write_entry = state[COMPLETE_SUCCESS];
    assign mmu.is_fault = state[COMPLETE_FAULT];

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    `ifdef ENABLE_SIMULATION_ASSERTIONS
        mmu_spurious_l1_response:
            assert property (@(posedge clk) disable iff (rst) (l1_response.data_valid) |-> (state[WAIT_REQUEST_1] | state[WAIT_REQUEST_2]))
            else $error("mmu recieved response without a request");
    `endif

    //TLB request remains high until it recieves a response from the MMU unless
    //the transaction is aborted.  As such, if TLB request is low and we are not in the
    //IDLE state, then our current processor state has been corrupted
    mmu_tlb_state_mismatch:
        assert property (@(posedge clk) disable iff (rst) (~mmu.request) |-> (state[IDLE]))
        else $error("MMU and TLB state mismatch");

endmodule
