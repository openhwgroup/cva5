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
        l1_arbiter_return_interface.master l1_response,
        output mmu_exception
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

    logic [31:0] request_addr;
    logic [19:0] request_addr_input_a;
    logic [9:0] request_addr_input_b;

    logic privilege_check;
    logic permissions_check;

    logic second_request;
    logic access_exception;
    typedef enum logic[1:0] {IDLE, REQUEST, WAIT} mmu_state_t;
    mmu_state_t mmu_state;

    assign l1_request.rnw = 1;
    assign l1_request.be = '1;
    assign l1_request.size = '0;
    assign l1_request.is_amo = 0;
    assign l1_request.amo = 0;

    pte_t pte;
    assign pte = l1_response.data;

    assign mmu_exception = access_exception;

    //assign request_addr = (mmu_state == IDLE) ? {mmu.ppn[19:0], 12'd0} + {mmu.virtual_address[31:22], 2'b00} : {pte.ppn1,pte.ppn0, 12'd0} + {mmu.virtual_address[21:12], 2'b00};
    assign request_addr_input_a = (mmu_state == IDLE) ? mmu.ppn[19:0] : {pte.ppn1[9:0],pte.ppn0};
    assign request_addr_input_b = (mmu_state == IDLE) ? mmu.virtual_address[31:22] : mmu.virtual_address[21:12];
    assign request_addr = {request_addr_input_a, 12'd0} + {request_addr_input_b, 2'b00};

    always_ff @ (posedge clk) begin
        mmu. new_phys_addr[19:10] <= pte.ppn1[9:0];

        if (~l1_request.request)
            l1_request.addr <= request_addr;

        if (second_request)
            mmu. new_phys_addr[9:0] <= pte.ppn0;
        else
            mmu. new_phys_addr[9:0] <= mmu.virtual_address[21:12];
    end

    //Not ((user-mode and non-user page) OR (supervisor-mode and user-page and user protected))
    assign privilege_check = !(
            ((mmu.privilege == USER_PRIVILEGE) && ~pte.u) |
            ((mmu.privilege == SUPERVISOR_PRIVILEGE) && pte.u && mmu.pum)
            );

    assign permissions_check = privilege_check & ((mmu.execute & pte.x) | //execute and exec bit set
        (~mmu.execute & //load-store
                ((mmu.rnw & (pte.r | (pte.x & mmu.mxr))) | //read and (read bit set or (execute and MXR))
                (~mmu.rnw & pte.w))));

    always_ff @ (posedge clk) begin
        if (rst) begin
            mmu_state <= IDLE;
            l1_request.request <= 0;
            mmu.write_entry <= 0;
            second_request <= 0;
            access_exception <= 0;
        end
        else begin
            unique case (mmu_state)
                IDLE: begin
                    mmu.write_entry <= 0;
                    second_request <= 0;
                    access_exception <= 0;
                    if (mmu.new_request & ~mmu.write_entry) begin //~mmu.write_entry for handshaking
                        mmu_state <= REQUEST;
                        l1_request.request <= 1;
                    end
                end
                REQUEST: begin
                    if (l1_request.ack) begin
                        mmu_state <= WAIT;
                        l1_request.request <= 0;
                    end
                end
                WAIT: begin
                    if (l1_response.data_valid) begin
                        if (~pte.v | (~pte.r & pte.w) | (~pte.r & ~pte.x & second_request)) begin //invalid pte
                            mmu_state <= IDLE;
                            access_exception <= 1;
                        end
                        else if (pte.r | pte.x) begin //leaf pte found
                            mmu_state <= IDLE;
                            if (permissions_check)
                                mmu.write_entry <= 1;
                            else
                                access_exception <= 1;
                        end
                        else begin //Non-leaf pte, request next level
                            mmu_state <= REQUEST;
                            l1_request.request <= 1;
                            second_request <= 1;
                        end
                    end
                end
            endcase
        end
    end


endmodule
