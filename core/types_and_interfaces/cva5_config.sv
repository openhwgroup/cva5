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

package cva5_config;

    ////////////////////////////////////////////////////
    //Vendor Selection
    typedef enum {
        XILINX = 0,
        INTEL = 1
    } vendor_config_t;
    localparam vendor_config_t FPGA_VENDOR = XILINX;

    ////////////////////////////////////////////////////
    //CSR Options
    typedef enum {
        BARE,
        M,
        MU,
        MSU
    } modes_t;

    typedef struct packed {
        bit [31:0] MACHINE_IMPLEMENTATION_ID;
        bit [31:0] CPU_ID;
        bit [31:0] RESET_VEC; //PC value on reset
        bit [31:0] RESET_TVEC;
        bit [31:0] MCONFIGPTR;
        bit INCLUDE_ZICNTR;
        bit INCLUDE_ZIHPM;
        bit INCLUDE_SSTC;
        bit INCLUDE_SMSTATEEN;
    } csr_config_t;

    //Memory range [L, H]
    //Address range is inclusive and must be aligned to its size
    typedef struct packed {
        logic [31:0] L;
        logic [31:0] H;
    } memory_config_t;

    //Atomic configuration
    typedef struct packed {
        int unsigned LR_WAIT; //Must be >= the maximum number of cycles a constrained LR-SC can take
        int unsigned RESERVATION_WORDS; //The amount of 32-bit words that are reserved by an LR instruction, must be == cache line size (if cache present)
    } amo_config_t;

    ////////////////////////////////////////////////////
    //Cache Options
    //Size in bytes: (LINES * WAYS * LINE_W * 4)
    //For optimal BRAM packing, LINES should not be less than 512
    typedef struct packed {
        int unsigned LINES;
        int unsigned LINE_W;// In words
        int unsigned WAYS;
        bit USE_EXTERNAL_INVALIDATIONS;
        bit USE_NON_CACHEABLE;
        memory_config_t NON_CACHEABLE;
    } cache_config_t;

    typedef struct packed {
        int unsigned LINE_ADDR_W;
        int unsigned SUB_LINE_ADDR_W;
        int unsigned TAG_W;
    } derived_cache_config_t;

    ////////////////////////////////////////////////////
    //Branch Predictor Options
    typedef struct packed {
        int unsigned WAYS;
        int unsigned ENTRIES;//min512
        int unsigned RAS_ENTRIES;
    } branch_predictor_config_t;

    ////////////////////////////////////////////////////
    //Bus Options
    typedef enum {
        AXI_BUS,
        AVALON_BUS,
        WISHBONE_BUS
    } peripheral_bus_type_t;

    ////////////////////////////////////////////////////
    //TLB Options
    typedef struct packed {
        int unsigned WAYS;
        int unsigned DEPTH;
    } tlb_config_t;

    ////////////////////////////////////////////////////
    //Unit IDs
    //To add a new unit update:
    //   - MAX_NUM_UNITS
    //   - units_t
    //   - unit_id_enum_t
    //ensuring that the bit index in units_t matches the enum value in unit_id_enum_t
    //Additionally, writeback units must be grouped before non-writeback units
    localparam MAX_NUM_UNITS = 9;
    typedef struct packed {
        bit GC;
        bit BR;
        //End of Write-Back Units
        bit CUSTOM;
        bit FPU;
        bit CSR;
        bit DIV;
        bit MUL;
        bit LS;
        bit ALU;
    } units_t;

    typedef enum bit [$clog2(MAX_NUM_UNITS)-1:0] {
        GC_ID = 8,
        BR_ID = 7,
        //End of Write-Back Units (insert new writeback units here)
        CUSTOM_ID = 6,
        FPU_ID = 5,
        CSR_ID = 4,
        DIV_ID = 3,
        MUL_ID = 2,
        LS_ID = 1,
        ALU_ID = 0
    } unit_id_enum_t;
    localparam unit_id_enum_t NON_WRITEBACK_ID = BR_ID;

    //WB Group config
    //  First index is write-back port
    //  Second index is position within the write-back port (Priority selection, with highest priority for index 0)
    //  See EXAMPLE_WB_GROUP_CONFIG below for an example of how to specify the configuration
    typedef unit_id_enum_t [MAX_NUM_UNITS-1:0][MAX_NUM_UNITS-1:0] wb_group_config_t;

    //Convenience function for determining how many writeback units are in each writeback group
    function int unsigned get_num_wb_units (input unit_id_enum_t [MAX_NUM_UNITS-1:0] ids);
        get_num_wb_units = 0;
        for (int i = 0; i < MAX_NUM_UNITS; i++)
            if (ids[i] != NON_WRITEBACK_ID)
                get_num_wb_units++;
    endfunction

    //Convenience function for turning the enum-based WB grouping into the units_t bit-vector representation
    //used in decode stage to determine the writeback group for the current instruction
    function units_t [MAX_NUM_UNITS-1:0] get_wb_units_type_representation(input wb_group_config_t ids);
        get_wb_units_type_representation = '{default : '0};
        for (int i = 0; i < MAX_NUM_UNITS; i++)
            for (int j = 0; j < MAX_NUM_UNITS; j++)
                if (ids[i][j] != NON_WRITEBACK_ID)
                    get_wb_units_type_representation[i][ids[i][j]] = 1;
    endfunction

    typedef struct packed {
        //ISA options
        modes_t MODES;

        bit INCLUDE_IFENCE; //local mem operations only
        bit INCLUDE_AMO;
        bit INCLUDE_CBO; //Data cache invalidation operations

        //Units
        units_t INCLUDE_UNIT; //Value of ALU, LS, BR, and GC ignored
    
        //CSR constants
        csr_config_t CSRS;
        //Memory Options
        int unsigned SQ_DEPTH;//CAM-based reasonable max of 4
        bit INCLUDE_FORWARDING_TO_STORES;
        amo_config_t AMO_UNIT;
        //Caches
        bit INCLUDE_ICACHE;
        cache_config_t ICACHE;
        memory_config_t ICACHE_ADDR;
        tlb_config_t ITLB;
        bit INCLUDE_DCACHE;
        cache_config_t DCACHE;
        memory_config_t DCACHE_ADDR;
        tlb_config_t DTLB;
        //Local memory
        bit INCLUDE_ILOCAL_MEM;
        memory_config_t ILOCAL_MEM_ADDR;
        bit INCLUDE_DLOCAL_MEM;
        memory_config_t DLOCAL_MEM_ADDR;
        //Instruction bus
        bit INCLUDE_IBUS;
        memory_config_t IBUS_ADDR;
        //Peripheral bus
        bit INCLUDE_PERIPHERAL_BUS;
        memory_config_t PERIPHERAL_BUS_ADDR;
        peripheral_bus_type_t PERIPHERAL_BUS_TYPE;
        //Branch Predictor Options
        bit INCLUDE_BRANCH_PREDICTOR;
        branch_predictor_config_t BP;
        //Writeback Options
        int unsigned NUM_WB_GROUPS;
        wb_group_config_t WB_GROUP;
    } cpu_config_t;

    //Function to generate derived cache parameters
    //Tag width based off of memory size and cache parameters
    function derived_cache_config_t get_derived_cache_params (input cpu_config_t cpu, input cache_config_t cache, input memory_config_t addr);
        return '{
            LINE_ADDR_W : $clog2(cache.LINES),
            SUB_LINE_ADDR_W : $clog2(cache.LINE_W),
            TAG_W : $clog2(64'(addr.H)-64'(addr.L)+1) - $clog2(cache.LINES) - $clog2(cache.LINE_W) - 2
        };
    endfunction

    ////////////////////////////////////////////////////
    //Example Config
    //  ALU requires its own WB port
    //  LS unit must be the first unit on its writeback port (LS unit does not use ack signal for timing considerations)
    //  Index in group is the priority order (highest priority for index zero)
    //  For optimal resource usage, there should be no holes in the write-back unit ordering
    //    (i.e. if a unit is often not included, either remove from the WB config or place at the end of a writeback group)
    localparam wb_group_config_t EXAMPLE_WB_GROUP_CONFIG = '{
        0 : '{0: ALU_ID, default : NON_WRITEBACK_ID},
        1 : '{0: LS_ID, default : NON_WRITEBACK_ID},
        2 : '{0: MUL_ID, 1: DIV_ID, 2: CSR_ID, 3: FPU_ID, 4: CUSTOM_ID, default : NON_WRITEBACK_ID},
        default : '{default : NON_WRITEBACK_ID}
    };

    localparam cpu_config_t EXAMPLE_CONFIG = '{
        //ISA options
        MODES : MSU,
        INCLUDE_UNIT : '{
            MUL : 1,
            DIV : 1,
            CSR : 1,
            FPU : 1,
            CUSTOM : 0,
            default: '0
        },
        INCLUDE_IFENCE : 1,
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
            INCLUDE_ZIHPM : 1,
            INCLUDE_SSTC : 1,
            INCLUDE_SMSTATEEN : 1
        },
        //Memory Options
        SQ_DEPTH : 4,
        INCLUDE_FORWARDING_TO_STORES : 1,
        AMO_UNIT : '{
            LR_WAIT : 32,
            RESERVATION_WORDS : 8
        },
        INCLUDE_ICACHE : 1,
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
        INCLUDE_DCACHE : 1,
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
        INCLUDE_ILOCAL_MEM : 0,
        ILOCAL_MEM_ADDR : '{
            L : 32'h80000000, 
            H : 32'h8FFFFFFF
        },
        INCLUDE_DLOCAL_MEM : 0,
        DLOCAL_MEM_ADDR : '{
            L : 32'h80000000,
            H : 32'h8FFFFFFF
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
        WB_GROUP : EXAMPLE_WB_GROUP_CONFIG
    };

    ////////////////////////////////////////////////////
    //Bus Options
    parameter C_M_AXI_ADDR_WIDTH = 32; //Kept as parameter, due to localparam failing with scripted IP packaging
    parameter C_M_AXI_DATA_WIDTH = 32; //Kept as parameter, due to localparam failing with scripted IP packaging

    ////////////////////////////////////////////////////
    //ID limit
    //MAX_IDS restricted to a power of 2
    localparam MAX_IDS = 16; //8 sufficient for rv32imd configs

    ////////////////////////////////////////////////////
    //Number of commit ports
    localparam RETIRE_PORTS = 2; //min 1. (Non-powers of two supported) > 1 is recommended to allow stores to commit sooner
    localparam REGFILE_READ_PORTS = 2; //min 2, for RS1 and RS2. (Non-powers of two supported)
    typedef enum {
        RS1 = 0,
        RS2 = 1,
        RS3 = 2
    } rs_index_t;

    ////////////////////////////////////////////////////
    //FP number widths
    localparam EXPO_WIDTH = 11; //11 is compliant
    localparam FRAC_WIDTH = 52; //52 is compliant
    localparam EXPO_WIDTH_F = 8; //8 is compliant
    localparam FRAC_WIDTH_F = 23; //23 is compliant
    localparam GRS_WIDTH = FRAC_WIDTH*2; //Should be FRAC_WIDTH*2 for full compliance
    //Do not change these values, they are derived from the previous
    localparam FLEN = 1+EXPO_WIDTH+FRAC_WIDTH; //Single precision (32 bits)
    localparam FLEN_F = 1+EXPO_WIDTH_F+FRAC_WIDTH_F; //Double precision (64 bits)

    ////////////////////////////////////////////////////
    //Exceptions
    localparam NUM_EXCEPTION_SOURCES = 5; //LS, Branch, Illegal, CSR, GC
    //Stored in a ID table on issue, checked at retire
    typedef enum bit [2:0] {
        LS_EXCEPTION = 0,
        BR_EXCEPTION = 1,
        PRE_ISSUE_EXCEPTION = 2,
        CSR_EXCEPTION = 3,
        GC_EXCEPTION = 4
    } exception_sources_t;

endpackage
