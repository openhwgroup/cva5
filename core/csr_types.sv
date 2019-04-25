/*
 * Copyright © 2018 Eric Matthews,  Lesley Shannon
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

package csr_types;
    import taiga_config::*;
    import taiga_types::*;

    const bit[1:0] CSR_READ_ONLY = 2'b11;

    typedef enum bit [1:0] {
        USER_PRIVILEGE = 2'b00,
        SUPERVISOR_PRIVILEGE = 2'b01,
        //reserved
        MACHINE_PRIVILEGE = 2'b11
    } privilege_t;


    typedef struct packed {
        logic [1:0] rw_bits;
        logic [1:0] privilege;
        logic [1:0] subtype;
        logic [5:0] sub_addr;
    } csr_addr_t;

    //Constant registers
    typedef struct packed {
        logic[1:0] base; //RV32I
        logic[3:0] reserved;
        logic Z;
        logic Y;
        logic X;
        logic W;
        logic V;
        logic U;
        logic T;
        logic S; //Supervisor mode
        logic R;
        logic Q;
        logic P;
        logic O;
        logic N;
        logic M; //multiply divide
        logic L;
        logic K;
        logic J;
        logic I; //Base
        logic H;
        logic G;
        logic F;
        logic E;
        logic D;
        logic C;
        logic B;
        logic A; //Atomic
    } misa_t;



    typedef struct packed {
        logic sd;
        logic [7:0] zeros;
        logic tsr;
        logic tw;
        logic tvm;
        logic mxr;
        logic sum;
        logic mprv;
        logic [1:0] xs;
        logic [1:0] fs;
        logic [1:0] mpp;
        logic [1:0] zeros1;
        logic spp;
        logic mpie;
        logic zero2;
        logic spie;
        logic upie;
        logic mie;
        logic zero3;
        logic sie;
        logic uie;
    } mstatus_t;


    typedef struct packed {
        logic [32-1:12] zeros;
        logic meip;
        logic zero1;
        logic seip;
        logic ueip;
        logic mtip;
        logic zero2;
        logic stip;
        logic utip;
        logic msip;
        logic zero3;
        logic ssip;
        logic usip;
    } mip_t;

    typedef struct packed {
        logic [32-1:12] zeros;
        logic meie;
        logic zero1;
        logic seie;
        logic ueie;
        logic mtie;
        logic zero2;
        logic stie;
        logic utie;
        logic msie;
        logic zero3;
        logic ssie;
        logic usie;
    } mie_t;

    typedef struct packed {
        logic interrupt;
        logic [XLEN-1-1-ECODE_W:0] zeroes;
        logic [ECODE_W-1:0] code;
    } mcause_t;


    typedef struct packed {
        logic mode;
        logic [ASIDLEN-1:0] asid;
        logic [21:0] ppn;
    } satp_t;


endpackage
