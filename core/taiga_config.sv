/*
 * Copyright © 2017-2019 Eric Matthews,  Lesley Shannon
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

package taiga_config;

    ////////////////////////////////////////////////////
    //Vendor Selection
    localparam FPGA_VENDOR = "xilinx"; //xilinx or intel
    ////////////////////////////////////////////////////
    //Privileged ISA Options

    //Enable Machine level privilege spec
    localparam ENABLE_M_MODE = 1;
    //Enable Supervisor level privilege spec
    localparam ENABLE_S_MODE = 0;
    //Enable User level privilege spec
    localparam ENABLE_U_MODE = 0;

    localparam MACHINE_IMPLEMENTATION_ID = 0;
    localparam CPU_ID = 0;//32-bit value
    localparam bit[31:0] RESET_VEC = 32'h80000000;

    //CSR counter width (33-64 bits): 48-bits --> 32 days @ 100MHz
    localparam COUNTER_W = 33;

    ////////////////////////////////////////////////////
    //ISA Options

    //Multiply and Divide Inclusion
    localparam USE_MUL = 1;
    localparam USE_DIV = 1;

    //Division algorithm selection
    typedef enum {
        RADIX_2,//Smallest
        QUICK_CLZ//Highest performance and best performance per LUT
    } div_type;
    localparam div_type DIV_ALGORITHM = QUICK_CLZ;

    //Enable Atomic extension (cache operations only)
    localparam USE_AMO = 0;


    ////////////////////////////////////////////////////
    //Memory Sources
    //Must select at least one source for instruction and data interfaces

    //Local memory
    localparam USE_I_SCRATCH_MEM = 1;
    localparam USE_D_SCRATCH_MEM = 1;

    //Peripheral bus
    typedef enum {
        AXI_BUS,
        AVALON_BUS,
        WISHBONE_BUS
    } bus_type_t;

    localparam USE_BUS = 1;
    localparam bus_type_t BUS_TYPE = AXI_BUS;

    //Caches
    localparam USE_DCACHE = 0;
    localparam USE_ICACHE = 0;


    ////////////////////////////////////////////////////
    //Address space
    localparam SCRATCH_ADDR_L = 32'h80000000;
    localparam SCRATCH_ADDR_H = 32'h8001FFFF;
    localparam SCRATCH_BIT_CHECK = 4;

    localparam MEMORY_ADDR_L = 32'h40000000;
    localparam MEMORY_ADDR_H = 32'h4FFFFFFF;
    localparam MEMORY_BIT_CHECK = 4;

    localparam BUS_ADDR_L = 32'h60000000;
    localparam BUS_ADDR_H = 32'h6FFFFFFF;
    localparam BUS_BIT_CHECK = 4;


    ////////////////////////////////////////////////////
    //Bus Options
    localparam C_M_AXI_ADDR_WIDTH = 32;
    localparam C_M_AXI_DATA_WIDTH = 32;


    ////////////////////////////////////////////////////
    //Instruction Cache Options
    //Size in bytes: (ICACHE_LINES * ICACHE_WAYS * ICACHE_LINE_W * 4)
    //For optimal BRAM packing, lines should not be less than 512
    localparam ICACHE_LINES = 512;
    localparam ICACHE_WAYS = 2;
    localparam ICACHE_LINE_ADDR_W = $clog2(ICACHE_LINES);
    localparam ICACHE_LINE_W = 4; //In words
    localparam ICACHE_SUB_LINE_ADDR_W = $clog2(ICACHE_LINE_W);
    localparam ICACHE_TAG_W = $clog2(64'(MEMORY_ADDR_H)-64'(MEMORY_ADDR_L)+1) - ICACHE_LINE_ADDR_W - ICACHE_SUB_LINE_ADDR_W - 2;


    ////////////////////////////////////////////////////
    //Data Cache Options
    //Size in bytes: (DCACHE_LINES * DCACHE_WAYS * DCACHE_LINE_W * 4)
    //For optimal BRAM packing, lines should not be less than 512
    localparam DCACHE_LINES = 512;
    localparam DCACHE_WAYS = 2;
    localparam DCACHE_LINE_ADDR_W = $clog2(DCACHE_LINES);
    localparam DCACHE_LINE_W = 4; //In words
    localparam DCACHE_SUB_LINE_ADDR_W = $clog2(DCACHE_LINE_W);
    localparam DCACHE_TAG_W = $clog2(64'(MEMORY_ADDR_H)-64'(MEMORY_ADDR_L)+1) - DCACHE_LINE_ADDR_W - DCACHE_SUB_LINE_ADDR_W - 2;

    localparam USE_DTAG_INVALIDATIONS = 0;


    ////////////////////////////////////////////////////
    //Instruction TLB Options
    localparam ITLB_WAYS = 2;
    localparam ITLB_DEPTH = 32;


    ////////////////////////////////////////////////////
    //Data TLB Options
    localparam DTLB_WAYS = 2;
    localparam DTLB_DEPTH = 32;
    ///////////////////////////////////////////////////


    ////////////////////////////////////////////////////
    //Branch Predictor Options
    localparam USE_BRANCH_PREDICTOR = 1;
    localparam BRANCH_PREDICTOR_WAYS = 2;
    localparam BRANCH_TABLE_ENTRIES = 512; //min 512
    localparam RAS_DEPTH = 8;


    ////////////////////////////////////////////////////
    //ID limit
    //MAX_IDS restricted to a power of 2
    localparam MAX_IDS = 8; //8 sufficient for rv32im configs

    ////////////////////////////////////////////////////
    //Number of commit ports
    localparam COMMIT_PORTS = 2; //min 2
    localparam REGFILE_READ_PORTS = 2; //min 2, for RS1 and RS2
    typedef enum logic {
        RS1 = 0,
        RS2 = 1
    } rs1_index_t;

    ////////////////////////////////////////////////////
    //Trace Options
    localparam ENABLE_TRACE_INTERFACE = 1;


    ////////////////////////////////////////////////////
    //L1 Arbiter IDs
    localparam L1_CONNECTIONS = 4;//USE_ICACHE + USE_DCACHE + ENABLE_S_MODE*2;
    localparam L1_DCACHE_ID = 0;
    localparam L1_DMMU_ID = 1;//ENABLE_S_MODE;
    localparam L1_ICACHE_ID = 2;//ENABLE_S_MODE + USE_DCACHE;
    localparam L1_IMMU_ID = 3;//ENABLE_S_MODE + USE_DCACHE + USE_ICACHE;


    ////////////////////////////////////////////////////
    //Write-Back Unit IDs
    localparam NUM_WB_UNITS = 2 + USE_MUL + USE_DIV;//ALU and LS
    localparam NUM_UNITS = NUM_WB_UNITS + 2;//Branch and CSRs

    localparam ALU_UNIT_WB_ID = 0;
    localparam LS_UNIT_WB_ID = 1;
    localparam DIV_UNIT_WB_ID = LS_UNIT_WB_ID + USE_DIV;
    localparam MUL_UNIT_WB_ID = DIV_UNIT_WB_ID + 1;
    //Non-writeback units
    localparam BRANCH_UNIT_ID = MUL_UNIT_WB_ID + 1;
    localparam GC_UNIT_ID = BRANCH_UNIT_ID + 1;

    ////////////////////////////////////////////////////

endpackage
