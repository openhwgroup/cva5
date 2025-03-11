/*
 * Copyright © 2024 Chris Keilbart
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

module cva5_wrapper

    import cva5_config::*;
    import cva5_types::*;

    #(
        parameter string LOCAL_MEM = "mem.mif",
        parameter int unsigned WORDS = 1024
    )
    (
        input logic clk,
        input logic rstn, //Synchronous active low

        //Peripheral AXI bus
        //AR
        input logic m_axi_arready,
        output logic m_axi_arvalid,
        output logic [31:0] m_axi_araddr,

        //R
        output logic m_axi_rready,
        input logic m_axi_rvalid,
        input logic [31:0] m_axi_rdata,
        input logic [1:0] m_axi_rresp,

        //AW
        input logic m_axi_awready,
        output logic m_axi_awvalid,
        output logic [31:0] m_axi_awaddr,

        //W
        input logic m_axi_wready,
        output logic m_axi_wvalid,
        output logic [31:0] m_axi_wdata,
        output logic [3:0] m_axi_wstrb,

        //B
        output logic m_axi_bready,
        input logic m_axi_bvalid,
        input logic [1:0] m_axi_bresp
    );

    //CPU connections
    local_memory_interface data_bram();
    local_memory_interface instruction_bram();
    axi_interface m_axi();
    avalon_interface m_avalon(); //Unused
    wishbone_interface dwishbone(); //Unused
    wishbone_interface iwishbone(); //Unused
    mem_interface mem();
    logic[63:0] mtime;
    interrupt_t s_interrupt; //Unused
    interrupt_t m_interrupt; //Unused

    ////////////////////////////////////////////////////
    //Implementation
    //Instantiates a CVA5 processor using local memory
    //Program start address 0x8000_0000
    //Local memory space from 0x8000_0000 through 0x80FF_FFFF
    //Peripheral bus from 0x6000_0000 through 0x6FFF_FFFF

    localparam wb_group_config_t WB_CPU_CONFIG = '{
        0 : '{0: ALU_ID, default : NON_WRITEBACK_ID},
        1 : '{0: LS_ID, default : NON_WRITEBACK_ID},
        2 : '{0: MUL_ID, 1: DIV_ID, 2: CSR_ID, 3: FPU_ID, 4: CUSTOM_ID, default : NON_WRITEBACK_ID},
        default : '{default : NON_WRITEBACK_ID}
    };

    localparam cpu_config_t CPU_CONFIG = '{
        //ISA options
        MODES : M,
        INCLUDE_UNIT : '{
            MUL : 1,
            DIV : 1,
            CSR : 1,
            FPU : 0,
            CUSTOM : 0,
            default: '0
        },
        INCLUDE_IFENCE : 0,
        INCLUDE_AMO : 0,
        INCLUDE_CBO : 0,
        //CSR constants
        CSRS : '{
            MACHINE_IMPLEMENTATION_ID : 0,
            CPU_ID : 0,
            RESET_VEC : 32'h80000000,
            RESET_TVEC : 32'h00000000,
            MCONFIGPTR : '0,
            INCLUDE_ZICNTR : 1,
            INCLUDE_ZIHPM : 0,
            INCLUDE_SSTC : 0,
            INCLUDE_SMSTATEEN : 0
        },
        //Memory Options
        SQ_DEPTH : 4,
        INCLUDE_FORWARDING_TO_STORES : 1,
        AMO_UNIT : '{
            LR_WAIT : 32,
            RESERVATION_WORDS : 8
        },
        INCLUDE_ICACHE : 0,
        ICACHE_ADDR : '{
            L: 32'h80000000,
            H: 32'h8FFFFFFF
        },
        ICACHE : '{
            LINES : 512,
            LINE_W : 4,
            WAYS : 2,
            USE_EXTERNAL_INVALIDATIONS : 0,
            USE_NON_CACHEABLE : 0,
            NON_CACHEABLE : '{
                L: 32'h70000000,
                H: 32'h7FFFFFFF
            }
        },
        ITLB : '{
            WAYS : 2,
            DEPTH : 64
        },
        INCLUDE_DCACHE : 0,
        DCACHE_ADDR : '{
            L: 32'h80000000,
            H: 32'h8FFFFFFF
        },
        DCACHE : '{
            LINES : 512,
            LINE_W : 4,
            WAYS : 2,
            USE_EXTERNAL_INVALIDATIONS : 0,
            USE_NON_CACHEABLE : 0,
            NON_CACHEABLE : '{
                L: 32'h70000000,
                H: 32'h7FFFFFFF
            }
        },
        DTLB : '{
            WAYS : 2,
            DEPTH : 64
        },
        INCLUDE_ILOCAL_MEM : 1,
        ILOCAL_MEM_ADDR : '{
            L : 32'h80000000, 
            H : 32'h80FFFFFF
        },
        INCLUDE_DLOCAL_MEM : 1,
        DLOCAL_MEM_ADDR : '{
            L : 32'h80000000,
            H : 32'h80FFFFFF
        },
        INCLUDE_IBUS : 0,
        IBUS_ADDR : '{
            L : 32'h60000000, 
            H : 32'h6FFFFFFF
        },
        INCLUDE_PERIPHERAL_BUS : 1,
        PERIPHERAL_BUS_ADDR : '{
            L : 32'h60000000,
            H : 32'h6FFFFFFF
        },
        PERIPHERAL_BUS_TYPE : AXI_BUS,
        //Branch Predictor Options
        INCLUDE_BRANCH_PREDICTOR : 1,
        BP : '{
            WAYS : 2,
            ENTRIES : 512,
            RAS_ENTRIES : 8
        },
        //Writeback Options
        NUM_WB_GROUPS : 3,
        WB_GROUP : WB_CPU_CONFIG
    };

    logic rst;
    assign rst = ~rstn;
    cva5 #(.CONFIG(CPU_CONFIG)) cpu(.*);

    always_ff @(posedge clk) begin
        if (rst)
            mtime <= '0;
        else
            mtime <= mtime + 1;
    end

    assign s_interrupt = '{default: '0};
    assign m_interrupt = '{default: '0};

    //AXI peripheral mapping; ID widths are missmatched but unused
    assign m_axi.arready = m_axi_arready;
    assign m_axi_arvalid = m_axi.arvalid;
    assign m_axi_araddr = m_axi.araddr;

    assign m_axi_rready = m_axi.rready;
    assign m_axi.rvalid = m_axi_rvalid;
    assign m_axi.rdata = m_axi_rdata;
    assign m_axi.rresp = m_axi_rresp;
    assign m_axi.rid = 6'b0;

    assign m_axi.awready = m_axi_awready;
    assign m_axi_awvalid = m_axi.awvalid;
    assign m_axi_awaddr = m_axi.awaddr;

    assign m_axi.wready = m_axi_wready;
    assign m_axi_wvalid = m_axi.wvalid;
    assign m_axi_wdata = m_axi.wdata;
    assign m_axi_wstrb = m_axi.wstrb;

    assign m_axi_bready = m_axi.bready;
    assign m_axi.bvalid = m_axi_bvalid;
    assign m_axi.bresp = m_axi_bresp;
    assign m_axi.bid = 6'b0;

    //Block memory
    localparam BRAM_ADDR_W = $clog2(WORDS);
    tdp_ram #(
        .ADDR_WIDTH(BRAM_ADDR_W),
        .NUM_COL(4),
        .COL_WIDTH(8),
        .PIPELINE_DEPTH(0),
        .CASCADE_DEPTH(8),
        .USE_PRELOAD(1),
        .PRELOAD_FILE(LOCAL_MEM)
    ) local_mem (
        .a_en(instruction_bram.en),
        .a_wbe(instruction_bram.be),
        .a_wdata(instruction_bram.data_in),
        .a_addr(instruction_bram.addr[BRAM_ADDR_W-1:0]),
        .a_rdata(instruction_bram.data_out),
        .b_en(data_bram.en),
        .b_wbe(data_bram.be),
        .b_wdata(data_bram.data_in),
        .b_addr(data_bram.addr[BRAM_ADDR_W-1:0]),
        .b_rdata(data_bram.data_out),
    .*);

endmodule
