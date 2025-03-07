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

module clint_wrapper

    #(
        parameter int unsigned NUM_CORES = 1,
        parameter logic AXI = 1'b1 //Else the wishbone bus is used
    ) (
        input logic clk,
        input logic rst,

        output logic[63:0] mtime,
        output logic[NUM_CORES-1:0] msip,
        output logic[NUM_CORES-1:0] mtip,

        //Address bits 31:16 are ignored, 1:0 assumed to be 00

        //Compliant Wishbone classic (not pipelined)
        input logic wb_cyc,
        input logic wb_stb,
        input logic wb_we,
        input logic [15:2] wb_adr,
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
    //Core Local INTerrupt unit (CLINT) wrapper
    //Handles addressing and bus interface
    //16-bit address space
    localparam logic [15:0] MSIP_BASE = 16'h0; //Must be 4-byte aligned
    localparam logic [15:0] MTIMECMP_BASE = 16'h4000; //Must be 8-byte aligned
    localparam logic [15:0] MTIME_BASE = 16'hbff8; //Must be 8-byte aligned
    localparam logic [15:0] CORES_MINUS_ONE = 16'(NUM_CORES-1);

    localparam CORE_W = NUM_CORES == 1 ? 1 : $clog2(NUM_CORES);

    logic[NUM_CORES-1:0][1:0][31:0] mtimecmp;
    logic write_mtime;
    logic write_mtimecmp;
    logic write_msip;
    logic write_upper;
    logic[CORE_W-1:0] write_msip_core;
    logic[CORE_W-1:0] write_mtimecmp_core;
    logic[31:0] write_data;
    logic[1:0][31:0] mtime_packed;
    assign mtime = {mtime_packed[1], mtime_packed[0]};

    clint #(.NUM_CORES(NUM_CORES)) core (
        .write_mtime(write_mtime),
        .write_mtimecmp(write_mtimecmp),
        .write_msip(write_msip),
        .write_upper(write_upper),
        .write_msip_core(write_msip_core),
        .write_mtimecmp_core(write_mtimecmp_core),
        .write_data(write_data),
        .mtime(mtime_packed),
        .mtimecmp(mtimecmp),
        .msip(msip),
        .mtip(mtip),
    .*);


    //Interface
    generate if (AXI) begin : gen_axi_if
        //Simple implementation uses state machine for reads and writes
        typedef enum logic[2:0] {
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
            unique case (state)
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
        logic doing_read;
        assign doing_read = state == RACCEPT;
        assign s_axi_arready = doing_read;
        assign s_axi_rvalid = state == RRESP;

        always_ff @(posedge clk) begin
            if (doing_read) begin
                case ({s_axi_araddr[15:2], 2'b00}) inside
                    [MSIP_BASE:MSIP_BASE+4*CORES_MINUS_ONE] : s_axi_rdata <= {31'b0, msip[NUM_CORES == 1 ? '0 : s_axi_araddr[2+:CORE_W]]};
                    [MTIME_BASE:MTIME_BASE+4] : s_axi_rdata <= mtime_packed[s_axi_araddr[2]];
                    [MTIMECMP_BASE:MTIMECMP_BASE+4+8*CORES_MINUS_ONE] : s_axi_rdata <= mtimecmp[NUM_CORES == 1 ? '0 : s_axi_araddr[3+:CORE_W]][s_axi_araddr[2]];
                    default : s_axi_rdata <= '0;
                endcase
            end
        end

        //Writes
        logic doing_write;
        assign doing_write = state == WACCEPT;
        assign s_axi_awready = doing_write;
        assign s_axi_wready = doing_write;
        assign s_axi_bvalid = state == WRESP;

        assign write_data = s_axi_wdata;
        assign write_upper = s_axi_awaddr[2];
        assign write_msip_core = NUM_CORES == 1 ? '0 : s_axi_awaddr[2+:CORE_W];
        assign write_mtimecmp_core = NUM_CORES == 1 ? '0 : s_axi_awaddr[3+:CORE_W];

        always_comb begin
            write_msip = 0;
            write_mtime = 0;
            write_mtimecmp = 0;
            case ({s_axi_awaddr[15:2], 2'b00}) inside
                [MSIP_BASE:MSIP_BASE+4*CORES_MINUS_ONE] : write_msip = doing_write;
                [MTIME_BASE:MTIME_BASE+4] : write_mtime = doing_write;
                [MTIMECMP_BASE:MTIMECMP_BASE+4+8*CORES_MINUS_ONE] : write_mtimecmp = doing_write;
            endcase
        end

        //Not in use
        assign wb_ack = 0;
    end else begin : gen_wishbone_if
        //Combinational response
        assign write_data = wb_dat_i;
        assign write_upper = wb_adr[2];
        assign wb_ack = wb_cyc & wb_stb;

        assign write_msip_core = NUM_CORES == 1 ? '0 : wb_adr[2+:CORE_W];
        assign write_mtimecmp_core = NUM_CORES == 1 ? '0 : wb_adr[3+:CORE_W];

        always_comb begin
            write_mtime = 0;
            write_mtimecmp = 0;
            write_msip = 0;
            wb_dat_o = '0;

            case ({wb_adr[15:2], 2'b00}) inside
                [MSIP_BASE:MSIP_BASE+4*CORES_MINUS_ONE] : begin
                    write_msip = wb_cyc & wb_stb & wb_we;
                    wb_dat_o = {31'b0, msip[write_msip_core]};
                end
                [MTIME_BASE:MTIME_BASE+4] : begin
                    write_mtime = wb_cyc & wb_stb & wb_we;
                    wb_dat_o = mtime_packed[write_upper];
                end
                [MTIMECMP_BASE:MTIMECMP_BASE+4+8*CORES_MINUS_ONE] : begin
                    write_mtimecmp = wb_cyc & wb_stb & wb_we;
                    wb_dat_o = mtimecmp[write_mtimecmp_core][write_upper];
                end
            endcase
        end

        //Not in use
        assign s_axi_awready = 0;
        assign s_axi_wready = 0;
        assign s_axi_bvalid = 0;
        assign s_axi_arready = 0;
        assign s_axi_rvalid = 0;
    end endgenerate

endmodule