/*
 * Copyright © 2017 Eric Matthews, Chris Keilbart, Lesley Shannon
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

module local_mem_sub_unit

    import riscv_types::*;

    (
        input logic clk,
        input logic rst,

        output logic write_outstanding,
        input logic amo,
        input amo_t amo_type,
        amo_interface.subunit amo_unit,
        memory_sub_unit_interface.responder unit,
        local_memory_interface.master local_mem
    );

    //If amo is tied to 0 and amo_unit is disconnected the tools can optimize most of the logic away

    logic rmw;
    logic[31:2] rmw_addr;
    logic[31:0] rmw_rs2;
    amo_t rmw_op;
    logic sc_valid;
    logic sc_valid_r;
    
    assign write_outstanding = 0;

    assign sc_valid = amo & amo_type == AMO_SC_FN5 & amo_unit.reservation_valid;
    assign amo_unit.set_reservation = unit.new_request & amo & amo_type == AMO_LR_FN5;
    assign amo_unit.clear_reservation = unit.new_request;
    assign amo_unit.reservation = unit.addr;

    assign amo_unit.rmw_valid = rmw;
    assign amo_unit.op = rmw_op;
    assign amo_unit.rs1 = local_mem.data_out;
    assign amo_unit.rs2 = rmw_rs2;

    always_comb begin
        if (rmw) begin
            unit.ready = 0;
            local_mem.addr = rmw_addr;
            local_mem.en = 1;
            local_mem.be = '1;
            local_mem.data_in = amo_unit.rd;
            unit.data_out = local_mem.data_out;
        end else begin
            unit.ready = 1;
            local_mem.addr = unit.addr[31:2];
            local_mem.en = unit.new_request;
            local_mem.be = {4{unit.we | sc_valid}} & unit.be; //SC only writes when it succeeds
            local_mem.data_in = unit.data_in;
            unit.data_out = sc_valid_r ? 32'b1 : local_mem.data_out;
        end
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            unit.data_valid <= 0;
            rmw <= 0;
            sc_valid_r <= 0;
        end
        else begin
            unit.data_valid <= unit.new_request & unit.re;
            rmw <= unit.new_request & amo & ~(amo_type inside {AMO_LR_FN5, AMO_SC_FN5});
            sc_valid_r <= sc_valid;
        end
        rmw_addr <= unit.addr[31:2];
        rmw_rs2 <= unit.data_in;
        rmw_op <= amo_type;
    end

endmodule
