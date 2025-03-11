/*
 * Copyright © 2019 Eric Matthews, Chris Keilbart, Lesley Shannon
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module avalon_master

    import riscv_types::*;

    #(
        parameter int unsigned LR_WAIT = 32, //The number of cycles lock is held after an LR
        parameter logic INCLUDE_AMO = 1 //Required because the tools cannot fully optimize even if amo signals are tied off
    )
    (
        input logic clk,
        input logic rst,

        output logic write_outstanding,
        avalon_interface.master m_avalon,

        input logic amo,
        input amo_t amo_type,
        amo_interface.subunit amo_unit,
        memory_sub_unit_interface.responder ls
    );

    ////////////////////////////////////////////////////
    //Implementation
    typedef enum {
        READY,
        REQUESTING,
        REQUESTING_AMO_R,
        REQUESTING_AMO_M,
        REQUESTING_AMO_W,
        READY_LR,
        REQUESTING_SC
    } state_t;
    state_t current_state;

    logic[$clog2(LR_WAIT)-1:0] lock_counter;
    logic request_is_sc;
    assign request_is_sc = amo & amo_type == AMO_SC_FN5;

    assign amo_unit.set_reservation = ls.new_request & amo & amo_type == AMO_LR_FN5;
    assign amo_unit.clear_reservation = ls.new_request;
    assign amo_unit.reservation = ls.addr;
    assign amo_unit.rs1 = ls.data_out;
    assign amo_unit.rs2 = m_avalon.writedata;

    always_ff @(posedge clk) begin
        m_avalon.addr[1:0] <= '0;
        unique case (current_state)
            READY : begin //Accept any request
                ls.ready <= ~ls.new_request | request_is_sc;
                ls.data_out <= 32'b1;
                ls.data_valid <= ls.new_request & request_is_sc;
                m_avalon.addr[31:2] <= ls.addr[31:2];
                m_avalon.byteenable <= ls.be;
                m_avalon.writedata <= ls.data_in;
                m_avalon.read <= ls.new_request & ls.re & ~request_is_sc;
                m_avalon.write <= ls.new_request & ls.we;
                m_avalon.lock <= ls.new_request & amo;
                write_outstanding <= ls.new_request & (ls.we | amo);
                amo_unit.rmw_valid <= 0;
                amo_unit.op <= amo_type;
                lock_counter <= '0;
                if (ls.new_request & (~amo | amo_type == AMO_LR_FN5))
                    current_state <= REQUESTING;
                else if (ls.new_request & amo & amo_type != AMO_SC_FN5)
                    current_state <= REQUESTING_AMO_R;
            end
            REQUESTING : begin //Wait for response
                ls.ready <= ~m_avalon.waitrequest;
                ls.data_out <= m_avalon.readdata;
                ls.data_valid <= m_avalon.read & ~m_avalon.waitrequest;
                m_avalon.read <= m_avalon.read & m_avalon.waitrequest;
                m_avalon.write <= m_avalon.write & m_avalon.waitrequest;
                write_outstanding <= m_avalon.write & ~m_avalon.waitrequest;
                if (~m_avalon.waitrequest)
                    current_state <= m_avalon.lock ? READY_LR : READY;
            end
            REQUESTING_AMO_R : begin //Read for an AMO
                if (INCLUDE_AMO) begin
                    ls.data_out <= m_avalon.readdata;
                    ls.data_valid <= ~m_avalon.waitrequest;
                    m_avalon.read <= m_avalon.waitrequest;
                    amo_unit.rmw_valid <= ~m_avalon.waitrequest;
                    if (~m_avalon.waitrequest)
                        current_state <= REQUESTING_AMO_M;
                end
            end
            REQUESTING_AMO_M : begin //One cycle for computing the AMO write value
                if (INCLUDE_AMO) begin
                    ls.data_valid <= 0;
                    m_avalon.writedata <= amo_unit.rd;
                    m_avalon.write <= 1;
                    amo_unit.rmw_valid <= 0;
                    current_state <= REQUESTING_AMO_W;
                end
            end
            REQUESTING_AMO_W : begin //Write for an AMO
                if (INCLUDE_AMO) begin
                    ls.ready <= ~m_avalon.waitrequest;
                    m_avalon.write <= m_avalon.waitrequest;
                    m_avalon.lock <= m_avalon.waitrequest;
                    write_outstanding <= m_avalon.waitrequest;
                    if (~m_avalon.waitrequest)
                        current_state <= READY;
                end
            end
            READY_LR : begin //Lock is held; hold for LR_WAIT cycles
                if (INCLUDE_AMO) begin
                    ls.ready <= ~ls.new_request | (request_is_sc & ~amo_unit.reservation_valid);
                    ls.data_out <= {31'b0, ~amo_unit.reservation_valid};
                    ls.data_valid <= ls.new_request & request_is_sc;
                    m_avalon.addr[31:2] <= ls.addr[31:2];
                    m_avalon.byteenable <= ls.be;
                    m_avalon.writedata <= ls.data_in;
                    m_avalon.read <= ls.new_request & ls.re & ~request_is_sc;
                    m_avalon.write <= ls.new_request & (ls.we | (request_is_sc & amo_unit.reservation_valid));
                    
                    write_outstanding <= ls.new_request & (ls.we | amo);
                    amo_unit.rmw_valid <= 0;
                    amo_unit.op <= amo_type;

                    if (ls.new_request)
                        m_avalon.lock <= amo;
                    else if (32'(lock_counter) == LR_WAIT-1)
                        m_avalon.lock <= 0;

                    lock_counter <= lock_counter + 1;

                    if (ls.new_request & (~amo | amo_type == AMO_LR_FN5))
                        current_state <= REQUESTING;
                    else if (ls.new_request & amo & amo_type != AMO_SC_FN5)
                        current_state <= REQUESTING_AMO_R;
                    else if (ls.new_request & amo & amo_type == AMO_SC_FN5 & amo_unit.reservation_valid)
                        current_state <= REQUESTING_SC;
                    else if (32'(lock_counter) == LR_WAIT-1 | ls.new_request)
                        current_state <= READY;
                end
            end
            REQUESTING_SC : begin //Exclusive write
                if (INCLUDE_AMO) begin
                    ls.ready <= ~m_avalon.waitrequest;
                    ls.data_valid <= 0;
                    m_avalon.write <= m_avalon.waitrequest;
                    m_avalon.lock <= m_avalon.waitrequest;
                    write_outstanding <= m_avalon.waitrequest;
                    if (~m_avalon.waitrequest)
                        current_state <= REQUESTING;
                end
            end
        endcase
        if (rst)
            current_state <= READY;
    end

endmodule
