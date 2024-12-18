/*
 * Copyright © 2023 Eric Matthews
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



package nexys_config;
    import cva5_config::*;

    localparam wb_group_config_t NEXYS_WB_GROUP_CONFIG = '{
        0 : '{0: ALU_ID, default : NON_WRITEBACK_ID},
        1 : '{0: LS_ID, default : NON_WRITEBACK_ID},
        2 : '{0: MUL_ID, 1: DIV_ID, 2: CSR_ID, 3: FPU_ID, 4: CUSTOM_ID, default : NON_WRITEBACK_ID},
        default : '{default : NON_WRITEBACK_ID}
    };

    localparam cpu_config_t NEXYS_CONFIG = '{
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
            INCLUDE_ZIHPM : 1,
            INCLUDE_SSTC : 1,
            INCLUDE_SMSTATEEN : 1
        },
        //Memory Options
        SQ_DEPTH : 8,
        INCLUDE_FORWARDING_TO_STORES : 1,
        AMO_UNIT : '{
            LR_WAIT : 32,
            RESERVATION_WORDS : 8 //Must be the same size as the DCACHE line width
        },
        INCLUDE_ICACHE : 1,
        ICACHE_ADDR : '{
            L : 32'h80000000, 
            H : 32'h87FFFFFF
        },
        ICACHE : '{
            LINES : 256,
            LINE_W : 8,
            WAYS : 2,
            USE_EXTERNAL_INVALIDATIONS : 0,
            USE_NON_CACHEABLE : 0,
            NON_CACHEABLE : '{
                L : 32'h88000000, 
                H : 32'h8FFFFFFF
            }
        },
        ITLB : '{
            WAYS : 2,
            DEPTH : 64
        },
        INCLUDE_DCACHE : 1,
        DCACHE_ADDR : '{
            L : 32'h80000000, 
            H : 32'h8FFFFFFF
        },
        DCACHE : '{
            LINES : 512,
            LINE_W : 8,
            WAYS : 1,
            USE_EXTERNAL_INVALIDATIONS : 0,
            USE_NON_CACHEABLE : 1,
            NON_CACHEABLE : '{
                L : 32'h88000000, 
                H : 32'h8FFFFFFF
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
            L : 32'h00000000, 
            H : 32'hFFFFFFFF
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
        WB_GROUP : NEXYS_WB_GROUP_CONFIG
    };

endpackage