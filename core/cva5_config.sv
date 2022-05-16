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
    typedef struct packed {
        int unsigned  COUNTER_W; //CSR counter width (33-64 bits): 48-bits --> 32 days @ 100MHz
        bit MCYCLE_WRITEABLE;
        bit MINSTR_WRITEABLE;
        bit MTVEC_WRITEABLE;
        bit INCLUDE_MSCRATCH;
        bit INCLUDE_MCAUSE;
        bit INCLUDE_MTVAL;
    } csr_non_standard_config_t;

    typedef struct packed {
        bit [31:0] MACHINE_IMPLEMENTATION_ID;
        bit [31:0] CPU_ID;
        bit [31:0] RESET_VEC; //PC value on reset
        bit [31:0] RESET_MTVEC;
        csr_non_standard_config_t NON_STANDARD_OPTIONS;
    } csr_config_t;

    //Memory range [L, H]
    //Address range is inclusive and must be aligned to its size
    typedef struct packed {
        bit [31:0] L;
        bit [31:0] H;
    } memory_config_t;

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

    typedef struct packed {
        //ISA options
        bit INCLUDE_M_MODE;
        bit INCLUDE_S_MODE;
        bit INCLUDE_U_MODE;
        bit INCLUDE_MUL;
        bit INCLUDE_DIV;
        bit INCLUDE_IFENCE; //local mem operations only
        bit INCLUDE_CSRS;
        bit INCLUDE_AMO; //cache operations only
        //CSR constants
        csr_config_t CSRS;
        //Memory Options
        int unsigned SQ_DEPTH;//CAM-based reasonable max of 4
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


    localparam cpu_config_t EXAMPLE_CONFIG = '{
        //ISA options
        INCLUDE_M_MODE : 1,
        INCLUDE_S_MODE : 1,
        INCLUDE_U_MODE : 1,
        INCLUDE_MUL : 1,
        INCLUDE_DIV : 1,
        INCLUDE_IFENCE : 1,
        INCLUDE_CSRS : 1,
        INCLUDE_AMO : 0,
        //CSR constants
        CSRS : '{
            MACHINE_IMPLEMENTATION_ID : 0,
            CPU_ID : 0,
            RESET_VEC : 32'h80000000,
            RESET_MTVEC : 32'h80000100,
            NON_STANDARD_OPTIONS : '{
                COUNTER_W : 33,
                MCYCLE_WRITEABLE : 1,
                MINSTR_WRITEABLE : 1,
                MTVEC_WRITEABLE : 1,
                INCLUDE_MSCRATCH : 1,
                INCLUDE_MCAUSE : 1,
                INCLUDE_MTVAL : 1
            }
        },
        //Memory Options
        SQ_DEPTH : 4,
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
            H : 32'h8FFFFFFF
        },
        INCLUDE_DLOCAL_MEM : 1,
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
        NUM_WB_GROUPS : 2
    };

    ////////////////////////////////////////////////////
    //Unit IDs
    typedef struct packed {
        int unsigned ALU;
        int unsigned LS;
        int unsigned CSR;
        int unsigned MUL;
        int unsigned DIV;
        int unsigned BR;
        int unsigned IEC;
    } unit_id_param_t;

    localparam unit_id_param_t EXAMPLE_UNIT_IDS = '{
        ALU : 0,
        LS : 1,
        CSR : 2,
        MUL : 3,
        DIV : 4,
        BR : 5,
        IEC : 6
    };

    ////////////////////////////////////////////////////
    //Bus Options
    parameter C_M_AXI_ADDR_WIDTH = 32; //Kept as parameter, due to localparam failing with scripted IP packaging
    parameter C_M_AXI_DATA_WIDTH = 32; //Kept as parameter, due to localparam failing with scripted IP packaging

    ////////////////////////////////////////////////////
    //ID limit
    //MAX_IDS restricted to a power of 2
    localparam MAX_IDS = 8; //8 sufficient for rv32im configs

    ////////////////////////////////////////////////////
    //Number of commit ports
    localparam RETIRE_PORTS = 2; //min 1. (Non-powers of two supported) > 1 is recommended to allow stores to commit sooner
    localparam REGFILE_READ_PORTS = 2; //min 2, for RS1 and RS2. (Non-powers of two supported)
    typedef enum bit {
        RS1 = 0,
        RS2 = 1
    } rs1_index_t;


    ////////////////////////////////////////////////////
    //Exceptions
    localparam NUM_EXCEPTION_SOURCES = 3; //LS, Branch, Illegal
    //Stored in a ID table on issue, checked at retire
    typedef enum bit [1:0] {
        LS_EXCEPTION = 0,
        BR_EXCEPTION = 1,
        PRE_ISSUE_EXCEPTION = 2
    } exception_sources_t;

    ////////////////////////////////////////////////////
    //Trace Options
    //Trace interface is necessary for verilator simulation
    localparam ENABLE_TRACE_INTERFACE = 1;


    ////////////////////////////////////////////////////
    //L1 Arbiter IDs
    localparam L1_CONNECTIONS = 4;
    typedef enum bit [1:0] {
        L1_DCACHE_ID = 0,
        L1_DMMU_ID = 1,
        L1_ICACHE_ID = 2,
        L1_IMMU_ID = 3
    } l1_id_t;

    ////////////////////////////////////////////////////
    //Debug Parameters

    //To enable assertions specific to formal debug, uncomment or set in tool flow
    //`define ENABLE_FORMAL_ASSERTIONS

    //To enable assertions specific to simulation (verilator), uncomment or set in tool flow
    //`define ENABLE_SIMULATION_ASSERTIONS

    //When no exceptions are expected in a simulation, turn on this flag
    //to convert any exceptions into assertions
    localparam DEBUG_CONVERT_EXCEPTIONS_INTO_ASSERTIONS = 0;

endpackage
