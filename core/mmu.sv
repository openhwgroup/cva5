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
import riscv_types::*;
import taiga_types::*;
import csr_types::*;

module mmu
    (
        input logic clk,
        input logic rst,
        mmu_interface.mmu mmu,
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

    typedef enum {IDLE, SEND_REQUEST_1, WAIT_REQUEST_1, SEND_REQUEST_2, WAIT_REQUEST_2, COMPLETE_SUCCESS, COMPLETE_FAULT} mmu_state_t;
    mmu_state_t state;
    mmu_state_t next_state;

    pte_t pte;
    logic access_valid;
    logic privilege_valid;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //L1 arbiter Interfrace
    assign l1_request.rnw = 1;
    assign l1_request.be = '1;
    assign l1_request.size = '0;
    assign l1_request.is_amo = 0;
    assign l1_request.amo = 0;

    always_ff @ (posedge clk) begin
        if (rst | l1_request.ack)
            l1_request.request <= 0;
        else if (next_state inside {SEND_REQUEST_1, SEND_REQUEST_2})
            l1_request.request <= 1;
    end

    always_ff @ (posedge clk) begin
        if (next_state == SEND_REQUEST_2)
            l1_request.addr <= {{pte.ppn1[9:0], pte.ppn0}, mmu.virtual_address[21:12], 2'b00};
        else
            l1_request.addr <= {mmu.ppn[19:0], mmu.virtual_address[31:22], 2'b00};
    end

    assign pte = l1_response.data;

    ////////////////////////////////////////////////////
    //Access and permission checks
    assign access_valid =
        (mmu.execute & pte.x) | //fetch
        (mmu.rnw & (pte.r | (pte.x & mmu.mxr))) | //load
        ((~mmu.rnw & ~mmu.execute) & pte.w); //store

    assign privilege_valid = 
        (mmu.privilege == MACHINE_PRIVILEGE) |
        ((mmu.privilege == SUPERVISOR_PRIVILEGE) & (~pte.u | (pte.u & mmu.sum))) |
        ((mmu.privilege == USER_PRIVILEGE) & pte.u);

    ////////////////////////////////////////////////////
    //State Machine
    always_comb begin
        next_state = state;
        case (state)
            IDLE : if (mmu.new_request) next_state = WAIT_REQUEST_1;
            SEND_REQUEST_1 : if (l1_request.ack) next_state = WAIT_REQUEST_1;
            WAIT_REQUEST_1 : begin
                if (l1_response.data_valid) begin
                    if (~pte.v | (~pte.r & pte.w)) //page not valid OR invalid xwr pattern
                        next_state = COMPLETE_FAULT;
                    else if (pte.v & (pte.r | pte.x)) //superpage (all remaining xwr patterns other than all zeros)
                        next_state = (access_valid & privilege_valid) ? COMPLETE_SUCCESS : COMPLETE_FAULT;
                    else //(pte.v & ~pte.x & ~pte.w & ~pte.r) pointer to next level in page table
                        next_state = SEND_REQUEST_2;
                end
            end
            SEND_REQUEST_2 : if (l1_request.ack) next_state = WAIT_REQUEST_2;
            WAIT_REQUEST_2 : if (l1_response.data_valid) next_state = (access_valid & privilege_valid) ? COMPLETE_SUCCESS : COMPLETE_FAULT;
            COMPLETE_SUCCESS : next_state = IDLE;
            COMPLETE_FAULT : next_state = IDLE;
            default : next_state = IDLE;
        endcase
    end

    always_ff @ (posedge clk) begin
        if (rst)
            state <= IDLE;
        else
            state <= next_state;
    end

    ////////////////////////////////////////////////////
    //TLB return path
    always_ff @ (posedge clk) begin
        if (l1_response.data_valid) begin
            mmu.new_phys_addr[19:10] <= pte.ppn1[9:0];
            mmu.new_phys_addr[9:0] <= (state == WAIT_REQUEST_2) ? pte.ppn0 : mmu.virtual_address[21:12];
        end
    end
    assign mmu.write_entry = (state == COMPLETE_SUCCESS);
    assign mmu.is_fault = (state == COMPLETE_FAULT);

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    mmu_spurious_l1_response:
        assert property (@(posedge clk) disable iff (rst) (l1_response.data_valid) |-> (state inside {WAIT_REQUEST_1, WAIT_REQUEST_2}))
        else $error("mmu recieved response without a request");

endmodule
