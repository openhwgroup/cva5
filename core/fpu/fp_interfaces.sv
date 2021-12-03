/*
 * Copyright © 2017, 2018, 2019 Eric Matthews,  Lesley Shannon
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
 *             Yuhui Gao <yuhuig@sfu.ca>
 */

import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import l2_config_and_types::*;
import fpu_types::*;

interface fp_renamer_interface #(parameter NUM_WB_GROUPS = 1);
    rs_addr_t rd_addr;
    rs_addr_t [FP_REGFILE_READ_PORTS-1:0] rs_addr;
    //logic [$clog2(NUM_WB_GROUPS)-1:0] rd_wb_group;
    logic rd_wb_group;
    logic uses_rd;
    id_t id;

    phys_addr_t [FP_REGFILE_READ_PORTS-1:0] phys_rs_addr;
    phys_addr_t phys_rd_addr;

    //logic [FP_REGFILE_READ_PORTS-1:0][$clog2(NUM_WB_GROUPS)-1:0] rs_wb_group;
    logic [FP_REGFILE_READ_PORTS-1:0] rs_wb_group;

    modport renamer (
        input rd_addr, rs_addr, rd_wb_group, uses_rd, id,
        output phys_rs_addr, rs_wb_group, phys_rd_addr
    );
    modport decode (
        input phys_rs_addr, rs_wb_group, phys_rd_addr,
        output rd_addr, rs_addr, rd_wb_group, uses_rd, id
    );
endinterface

interface fp_register_file_issue_interface #(parameter NUM_WB_GROUPS = 1);
    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;

    //read interface
    phys_addr_t phys_rs_addr [FP_REGFILE_READ_PORTS];
    //logic [$clog2(NUM_WB_GROUPS)-1:0] rs_wb_group [REGFILE_READ_PORTS];
    logic rs_wb_group [FP_REGFILE_READ_PORTS];
    logic [FLEN-1:0] data [FP_REGFILE_READ_PORTS];
    logic inuse [FP_REGFILE_READ_PORTS];

    //issue write interface
    phys_addr_t phys_rd_addr;
    logic single_cycle_or_flush;

    modport register_file (
        input phys_rs_addr, phys_rd_addr, single_cycle_or_flush, rs_wb_group,
        output data, inuse
    );
    modport issue (
        output phys_rs_addr, phys_rd_addr, single_cycle_or_flush, rs_wb_group,
        input data, inuse
    );
endinterface

interface fp_unit_issue_interface;
    logic possible_issue;
    logic new_request;
    logic new_request_r;
    id_t id;

    logic ready;

    modport decode (input ready, output possible_issue, new_request, new_request_r, id);
    modport unit (output ready, input possible_issue, new_request, new_request_r, id);
endinterface

interface fp_unit_writeback_interface;
        logic ack;

        id_t id;
        logic done;
        logic [FLEN-1:0] rd;
        logic [4:0] fflags;
        logic [2:0] rm;
        // shared with normalization
        logic carry;
        logic safe;
        logic hidden;
        logic [2:0] grs;
        fp_shift_amt_t clz;

        modport unit (
            input ack,
            output id, done, rd, fflags, rm, carry, hidden, grs, clz, safe
        );
        modport wb (
            output ack,
            input id, done, rd, fflags, rm, carry, hidden, grs, clz, safe
        );
endinterface

interface fp_load_store_queue_interface;

    logic [FLEN-1:0] data_in;
    logic forwarded_store;
    id_t data_id;
    id_t id_needed_by_store;
    fp_data_access_shared_inputs_t transaction_out;
    logic is_float;
    logic we;

    modport queue (input we, data_in, data_id, is_float, forwarded_store, output id_needed_by_store, transaction_out);
    modport ls (output we, data_in, data_id, is_float, forwarded_store, input id_needed_by_store, transaction_out);
endinterface

interface shared_decode_interface;
    logic float_need_int_rs1;
    logic int_rs1_conflict;
    rs_addr_t int_rs1_addr;
    logic [XLEN-1:0] int_rs1_data;
    logic fp_rs1_conflict;
    logic [FLEN-1:0] fp_rs1_data;
    rs_addr_t int_rs2_addr;
    id_t fp_store_forward_id;
    logic fp_issue_stage_valid;

    logic instruction_issued;
    logic fp_instruction_issued;
    id_t fp_issue_id;

    modport base (input fp_issue_id, fp_instruction_issued, fp_issue_stage_valid, float_need_int_rs1, fp_rs1_conflict, fp_rs1_data, fp_store_forward_id, int_rs1_addr, output int_rs1_conflict, int_rs1_data, int_rs2_addr, instruction_issued);

    modport float (output fp_issue_id, fp_instruction_issued, fp_issue_stage_valid, float_need_int_rs1, fp_rs1_conflict, fp_rs1_data, fp_store_forward_id, int_rs1_addr, input int_rs1_conflict, int_rs1_data, int_rs2_addr, instruction_issued);
endinterface

interface unsigned_sqrt_interface #(parameter DATA_WIDTH = 32);
    logic start;
    logic [DATA_WIDTH-1:0] radicand;
    logic [DATA_WIDTH-1:0] remainder;
    logic [DATA_WIDTH-1:0] quotient;
    logic done;
    logic early_terminate;
    modport requester (input remainder, quotient, done, output radicand, start, early_terminate);
    modport sqrt (output remainder, quotient, done, input radicand, start, early_terminate);
endinterface



