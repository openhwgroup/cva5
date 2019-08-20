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
    parameter FPGA_VENDOR = "xilinx"; //xilinx or intel


    ////////////////////////////////////////////////////
    //Privileged ISA Options

    //Enable Machine level privilege spec
    parameter ENABLE_M_MODE = 1;
    //Enable Supervisor level privilege spec
    parameter ENABLE_S_MODE = 0;

    parameter CPU_ID = 0;//32-bit value
    parameter bit[31:0] RESET_VEC = 32'h80000000;

    //CSR counter width (33-64 bits): 48-bits --> 32 days @ 100MHz
    parameter COUNTER_W = 33;

    ////////////////////////////////////////////////////
    //ISA Options

    //Multiply and Divide Inclusion
    parameter USE_MUL = 1;
    parameter USE_DIV = 1;

    //Division algorithm selection
    typedef enum {
        RADIX_2,
        RADIX_2_EARLY_TERMINATE,
        RADIX_2_EARLY_TERMINATE_FULL,
        RADIX_4,
        RADIX_4_EARLY_TERMINATE,
        RADIX_8,
        RADIX_8_EARLY_TERMINATE,
        RADIX_16,
        QUICK_NAIVE,
        QUICK_CLZ,
        QUICK_CLZ_MK2
    } div_type;
    parameter div_type DIV_ALGORITHM = QUICK_CLZ;

    //Enable Atomic extension (cache operations only)
    parameter USE_AMO = 0;


    ////////////////////////////////////////////////////
    //Memory Sources
    //Must select at least one source for instruction and data interfaces

    //Local memory
    parameter USE_I_SCRATCH_MEM = 1;
    parameter USE_D_SCRATCH_MEM = 1;

    //Peripheral bus
    typedef enum {
        AXI_BUS,
        AVALON_BUS,
        WISHBONE_BUS
    } bus_type_t;

    parameter USE_BUS = 1;
    parameter bus_type_t BUS_TYPE = AXI_BUS;

    //Caches
    parameter USE_DCACHE = 0;
    parameter USE_ICACHE = 0;


    ////////////////////////////////////////////////////
    //Address space
    parameter SCRATCH_ADDR_L = 32'h80000000;
    parameter SCRATCH_ADDR_H = 32'h800FFFFF;
    parameter SCRATCH_BIT_CHECK = 4;

    parameter MEMORY_ADDR_L = 32'h40000000;
    parameter MEMORY_ADDR_H = 32'h4FFFFFFF;
    parameter MEMORY_BIT_CHECK = 4;

    parameter BUS_ADDR_L = 32'h60000000;
    parameter BUS_ADDR_H = 32'h6FFFFFFF;
    parameter BUS_BIT_CHECK = 4;


    ////////////////////////////////////////////////////
    //Bus Options
    parameter C_M_AXI_ADDR_WIDTH = 32;
    parameter C_M_AXI_DATA_WIDTH = 32;


    ////////////////////////////////////////////////////
    //Instruction Cache Options
    //Size in bytes: (ICACHE_LINES * ICACHE_WAYS * ICACHE_LINE_W * 4)
    //For optimal BRAM packing, lines should not be less than 512
    parameter ICACHE_LINES = 512;
    parameter ICACHE_WAYS = 2;
    parameter ICACHE_LINE_ADDR_W = $clog2(ICACHE_LINES);
    parameter ICACHE_LINE_W = 4; //In words
    parameter ICACHE_SUB_LINE_ADDR_W = $clog2(ICACHE_LINE_W);
    parameter ICACHE_TAG_W = 32 - ICACHE_LINE_ADDR_W - ICACHE_SUB_LINE_ADDR_W - 2;


    ////////////////////////////////////////////////////
    //Data Cache Options
    //Size in bytes: (DCACHE_LINES * DCACHE_WAYS * DCACHE_LINE_W * 4)
    //For optimal BRAM packing, lines should not be less than 512
    parameter DCACHE_LINES = 512;
    parameter DCACHE_WAYS = 2;
    parameter DCACHE_LINE_ADDR_W = $clog2(DCACHE_LINES);
    parameter DCACHE_LINE_W = 4; //In words
    parameter DCACHE_SUB_LINE_ADDR_W = $clog2(DCACHE_LINE_W);
    parameter DCACHE_TAG_W = 32 - DCACHE_LINE_ADDR_W - DCACHE_SUB_LINE_ADDR_W - 2;

    parameter USE_DTAG_INVALIDATIONS = 0;


    ////////////////////////////////////////////////////
    //Instruction TLB Options
    parameter ITLB_WAYS = 2;
    parameter ITLB_DEPTH = 32;


    ////////////////////////////////////////////////////
    //Data TLB Options
    parameter DTLB_WAYS = 2;
    parameter DTLB_DEPTH = 32;
    ///////////////////////////////////////////////////


    ////////////////////////////////////////////////////
    //Branch Predictor Options
    parameter USE_BRANCH_PREDICTOR = 1;
    parameter BRANCH_PREDICTOR_WAYS = 2;
    parameter BRANCH_TABLE_ENTRIES = 512;
    parameter RAS_DEPTH = 8;


    ////////////////////////////////////////////////////
    //FIFO/Buffer Depths
    //All parameters restricted to powers of two
    parameter MAX_INFLIGHT_COUNT = 4;
    parameter FETCH_BUFFER_DEPTH = 4;

    parameter LS_INPUT_BUFFER_DEPTH = 4;
    parameter DIV_INPUT_BUFFER_DEPTH = 4;

    ////////////////////////////////////////////////////
    //Trace Options
    parameter ENABLE_TRACE_INTERFACE = 1;


    ////////////////////////////////////////////////////
    //L1 Arbiter IDs
    parameter L1_CONNECTIONS = 4;//USE_ICACHE + USE_DCACHE + ENABLE_S_MODE*2;
    parameter L1_DCACHE_ID = 0;
    parameter L1_DMMU_ID = 1;//ENABLE_S_MODE;
    parameter L1_ICACHE_ID = 2;//ENABLE_S_MODE + USE_DCACHE;
    parameter L1_IMMU_ID = 3;//ENABLE_S_MODE + USE_DCACHE + USE_ICACHE;


    ////////////////////////////////////////////////////
    //Write-Back Unit IDs
    parameter NUM_WB_UNITS = 4 + USE_MUL + USE_DIV;
    parameter WB_UNITS_WIDTH = $clog2(NUM_WB_UNITS);


    parameter ALU_UNIT_WB_ID = 0;
    parameter GC_UNIT_WB_ID = 1;//uses accepted
    parameter BRANCH_UNIT_WB_ID = 2;
    parameter LS_UNIT_WB_ID = 3;
    parameter DIV_UNIT_WB_ID = LS_UNIT_WB_ID + USE_DIV;
    parameter MUL_UNIT_WB_ID = DIV_UNIT_WB_ID + USE_MUL;
    ////////////////////////////////////////////////////

endpackage
