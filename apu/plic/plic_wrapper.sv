/*
 * Copyright © 2024 Chris Keilbart, Mohammad Shahidzadeh
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
 *             Mohammad Shahidzadeh <mohammad_shahidzadeh_asadi@sfu.ca>
 */

module plic_wrapper

    #(
        parameter int unsigned NUM_SOURCES = 1,
        parameter int unsigned NUM_TARGETS = 1,
        parameter int unsigned PRIORITY_W = 4,
        parameter int unsigned REG_STAGE = 1, //The stage in the comparison tree to insert registers at, must be 1 <= N <= clog2(NUM_SOURCES+1)
        parameter logic AXI = 1'b0 //Else the wishbone bus is used
    ) (
        input logic clk,
        input logic rst,

        input logic[NUM_SOURCES:1] irq_srcs,
        input logic[NUM_SOURCES-1:0] edge_sensitive, //Both rising and falling edges, else level sensitive and active high
        output logic[NUM_TARGETS-1:0] eip,

        //Address bits 31:26 are ignored, 1:0 assumed to be 00

        //Compliant Wishbone classic (not pipelined)
        input logic wb_cyc,
        input logic wb_stb,
        input logic wb_we,
        input logic [25:2] wb_adr,
        input logic [31:0] wb_dat_i,
        output logic [31:0] wb_dat_o,
        output logic wb_ack,

        //Compliant AXI Lite interface; does not include optional awprot, wstrb, bresp, arprot, and rresp
        input logic s_axi_awvalid,
        input logic[31:0] s_axi_awaddr,
        output logic s_axi_awready,
        input logic s_axi_wvalid,
        input logic[31:0] s_axi_wdata,
        output logic s_axi_wready,
        output logic s_axi_bvalid,
        input logic s_axi_bready,
        input logic s_axi_arvalid,
        input logic[31:0] s_axi_araddr,
        output logic s_axi_arready,
        output logic s_axi_rvalid,
        output logic[31:0] s_axi_rdata,
        input logic s_axi_rready
    );

    ////////////////////////////////////////////////////
    //RISC-V Platform-Level Interrupt Controller (PLIC) wrapper
    //Handles bus interface
    //26-bit address space

    //If the parameter is too large such that the register stage is skipped, force it lower to enforce correct functionality
    localparam int unsigned REG_STAGE_CORRECTED = REG_STAGE > $clog2(NUM_SOURCES+1)+1 ? 1 : REG_STAGE;

    logic read_reg;
    logic write_reg;
    logic[25:2] addr;
    logic[31:0] rdata;
    logic[31:0] wdata;

    plic #(
        .NUM_SOURCES(NUM_SOURCES),
        .NUM_TARGETS(NUM_TARGETS),
        .PRIORITY_W(PRIORITY_W),
        .REG_STAGE(REG_STAGE_CORRECTED)
    ) plic_inst (
        .irq_srcs(irq_srcs),
        .edge_sensitive(edge_sensitive),
        .read_reg(read_reg),
        .write_reg(write_reg),
        .addr(addr),
        .wdata(wdata),
        .rdata(rdata),
        .eip(eip),
    .*);


    //Interface
    generate if (AXI) begin : gen_axi_if
        //Simple implementation uses state machine for reads and writes
        typedef enum logic [2:0] {
            IDLE,
            RACCEPT,
            WACCEPT,
            RRESP,
            WRESP
        } state_t;
        state_t state;
        state_t next_state;

        always_ff @(posedge clk) begin
            if (rst)
                state <= IDLE;
            else
                state <= next_state;
        end

        always_comb begin
            unique case (state) inside
                IDLE : begin
                    if (s_axi_awvalid & s_axi_wvalid)
                        next_state = WACCEPT;
                    else if (s_axi_arvalid)
                        next_state = RACCEPT;
                    else
                        next_state = IDLE;
                end
                RACCEPT : next_state = RRESP;
                WACCEPT : next_state = WRESP;
                RRESP : next_state = s_axi_rready ? IDLE : RRESP;
                WRESP : next_state = s_axi_bready ? IDLE : WRESP;
            endcase
        end

        //Reads
        assign read_reg = state == RACCEPT;
        assign s_axi_arready = read_reg;
        assign s_axi_rvalid = state == RRESP;

        always_ff @(posedge clk) begin
            if (read_reg)
                s_axi_rdata <= rdata;
        end

        //Writes
        assign write_reg = state == WACCEPT;
        assign s_axi_awready = write_reg;
        assign s_axi_wready = write_reg;
        assign wdata = s_axi_wdata;
        assign s_axi_bvalid = state == WRESP;

        //Must use the read address while in the idle state to ensure read_reg claims the right interrupt
        assign addr = write_reg ? s_axi_awaddr[25:2] : s_axi_araddr[25:2];

        //Not in use
        assign wb_ack = 0;
    end else begin : gen_wishbone_if
        //Writes are asynchronous, reads need two cycles
        logic read_done;
        assign addr = wb_adr[25:2];
        assign wdata = wb_dat_i;
        assign write_reg = wb_cyc & wb_stb & wb_we;
        assign wb_ack = write_reg | read_done;

        always_ff @(posedge clk) begin
            read_reg <= wb_cyc & wb_stb & ~wb_we & ~read_reg & ~read_done;
            read_done <= read_reg;
            wb_dat_o <= rdata;
        end

        //Not in use
        assign s_axi_awready = 0;
        assign s_axi_wready = 0;
        assign s_axi_bvalid = 0;
        assign s_axi_arready = 0;
        assign s_axi_rvalid = 0;
    end endgenerate

endmodule
