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
        input logic S_AXI_awvalid,
        input logic[31:0] S_AXI_awaddr,
        output logic S_AXI_awready,
        input logic S_AXI_wvalid,
        input logic[31:0] S_AXI_wdata,
        output logic S_AXI_wready,
        output logic S_AXI_bvalid,
        input logic S_AXI_bready,
        input logic S_AXI_arvalid,
        input logic[31:0] S_AXI_araddr,
        output logic S_AXI_arready,
        output logic S_AXI_rvalid, 
        output logic[31:0] S_AXI_rdata,
        input logic S_AXI_rready
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
    generate if (AXI) begin : gen_S_AXI_if
        //Simple implementation uses single-cycle for reads and writes
        typedef enum logic [2:0] {
            IDLE,
            RADDR,
            WADDR,
            RDATA,
            WDATA
        } state_t;

        state_t state, next_state;

        always_ff @(posedge clk) begin
            if (rst) begin
                state <= IDLE;
            end
            else begin
                state <= next_state;
            end
        end

        always_comb begin
            next_state = state;
            case (state) inside
                IDLE : begin
                    if (S_AXI_awvalid) begin
                        next_state = WADDR;
                    end
                    else if (S_AXI_arvalid) begin
                        next_state = RADDR;
                    end
                end
                RADDR : begin
                    if (S_AXI_arready) begin
                        next_state = RDATA;
                    end
                end
                WADDR : begin
                    if (S_AXI_wvalid) begin
                        next_state = WDATA;
                    end
                end
                RDATA : begin
                    if (S_AXI_rready) begin
                        next_state = IDLE;
                    end
                end
                WDATA : begin
                    if (S_AXI_bready) begin
                        next_state = IDLE;
                    end
                end
            endcase
        end
        logic [31:0] raddr_reg,waddr_reg;
        logic doing_write;
        assign doing_write = (S_AXI_wvalid && (state==WDATA)) ? 1 : 0;
        assign S_AXI_arready = (state == RADDR) ? 1 : 0;
        assign S_AXI_rvalid = (state == RDATA) ? 1 : 0;
        assign S_AXI_awready = (state == WADDR) ? 1 : 0;
        assign S_AXI_wready = (state == WDATA) ? 1 : 0;
        assign S_AXI_bvalid = (state == WDATA) ? 1 : 0;
        always_ff @(posedge clk) begin
            if (rst) begin
                raddr_reg <= 0;
                waddr_reg <= 0;
            end
            else begin
                if(S_AXI_arvalid) begin
                    raddr_reg <= S_AXI_araddr;
                end
                if(S_AXI_awvalid) begin
                    waddr_reg <= S_AXI_awaddr;
                end
            end
        end
        //Read data
        always_ff @(posedge clk) begin
            case ({raddr_reg[15:2], 2'b00}) inside
                [MSIP_BASE:MSIP_BASE+4*CORES_MINUS_ONE] : S_AXI_rdata <= {31'b0, msip[NUM_CORES == 1 ? '0 : raddr_reg[2+:CORE_W]]};
                [MTIME_BASE:MTIME_BASE+4] : S_AXI_rdata <= mtime_packed[raddr_reg[2]];
                [MTIMECMP_BASE:MTIMECMP_BASE+4+8*CORES_MINUS_ONE] : S_AXI_rdata <= mtimecmp[NUM_CORES == 1 ? '0 : raddr_reg[3+:CORE_W]][raddr_reg[2]];
                default : S_AXI_rdata <= '0;
            endcase
        end

        //Write data
        assign write_data = S_AXI_wdata;
        assign write_upper = waddr_reg[2];
        assign write_msip_core = NUM_CORES == 1 ? '0 : waddr_reg[2+:CORE_W];
        assign write_mtimecmp_core = NUM_CORES == 1 ? '0 : waddr_reg[3+:CORE_W];
        
        always_comb begin
            write_msip = 0;
            write_mtime = 0;
            write_mtimecmp = 0;
            case ({waddr_reg[15:2], 2'b00}) inside
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
        assign S_AXI_awready = 0;
        assign S_AXI_wready = 0;
        assign S_AXI_bvalid = 0;
        assign S_AXI_arready = 0;
        assign S_AXI_rvalid = 0;
    end endgenerate

endmodule