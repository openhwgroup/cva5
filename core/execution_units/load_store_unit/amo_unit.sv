/*
 * Copyright © 2024 Chris Keilbart, Lesley Shannon
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module amo_unit

    import riscv_types::*;

    #(
        parameter int NUM_UNITS = 3,
        parameter int RESERVATION_WORDS = 4
    ) //TODO: reservation shape and size must be discoverable(?)
    (
        input logic clk,
        input logic rst,

        amo_interface.amo_unit agents[NUM_UNITS]
    );

    localparam RESERVATION_WIDTH = 30 - $clog2(RESERVATION_WORDS);
    typedef logic[RESERVATION_WIDTH-1:0] reservation_t;

    ////////////////////////////////////////////////////
    //Interface unpacking
    logic[NUM_UNITS-1:0] set_reservation;
    logic[NUM_UNITS-1:0] clear_reservation;
    reservation_t[NUM_UNITS-1:0] reservation;
    reservation_t lr_addr;
    logic lr_valid;

    logic[NUM_UNITS-1:0] rmw_valid;
    amo_t[NUM_UNITS-1:0] op;
    logic[NUM_UNITS-1:0][31:0] rs1;
    logic[NUM_UNITS-1:0][31:0] rs2;
    logic[31:0] rd;

    generate for (genvar i = 0; i < NUM_UNITS; i++) begin : gen_unpacking
        assign set_reservation[i] = agents[i].set_reservation;
        assign clear_reservation[i] = agents[i].clear_reservation;
        assign reservation[i] = agents[i].reservation[31-:RESERVATION_WIDTH];
        assign agents[i].reservation_valid = lr_valid & lr_addr == reservation[i];

        assign rmw_valid[i] = agents[i].rmw_valid;
        assign op[i] = agents[i].op;
        assign rs1[i] = agents[i].rs1;
        assign rs2[i] = agents[i].rs2;
        assign agents[i].rd = rd;
    end endgenerate

    ////////////////////////////////////////////////////
    //Multiplexing
    //Shared LR-SC and RMW port across all units
    reservation_t set_val;
    amo_t selected_op;
    logic[31:0] selected_rs1;
    logic[31:0] selected_rs2;
    logic[$clog2(NUM_UNITS > 1 ? NUM_UNITS : 2)-1:0] reservation_int;
    logic[$clog2(NUM_UNITS > 1 ? NUM_UNITS : 2)-1:0] rmw_int;
    
    one_hot_to_integer #(.C_WIDTH(NUM_UNITS)) reservation_conv (
        .one_hot(set_reservation),
        .int_out(reservation_int)
    );
    assign set_val = reservation[reservation_int];

    one_hot_to_integer #(.C_WIDTH(NUM_UNITS)) rmw_conv (
        .one_hot(rmw_valid),
        .int_out(rmw_int)
    );
    assign selected_op = op[rmw_int];
    assign selected_rs1 = rs1[rmw_int];
    assign selected_rs2 = rs2[rmw_int];

    ////////////////////////////////////////////////////
    //RISC-V LR-SC
    //One address is reserved at a time for all units
    //The reservation can be set or cleared at any time by any unit, but set has priority over clear on same cycle
    always_ff @(posedge clk) begin
        if (rst)
            lr_valid <= 0;
        else
            lr_valid <= (lr_valid & ~|clear_reservation) | |set_reservation;
        if (|set_reservation)
            lr_addr <= set_val;   
    end

    ////////////////////////////////////////////////////
    //RISC-V Atomic ALU
    //Combinational; results valid in same cycle
    amo_alu #(.WIDTH(32)) alu_inst (
        .amo_type(selected_op),
        .rs1(selected_rs1),
        .rs2(selected_rs2),
        .rd(rd)
    );

endmodule
