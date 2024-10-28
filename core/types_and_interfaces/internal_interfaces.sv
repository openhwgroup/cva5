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
 */

interface branch_predictor_interface;
    import cva5_types::*;

    //Fetch signals
    logic [31:0] if_pc;
    id_t if_id;
    logic new_mem_request;
    logic [31:0] next_pc;

    id_t pc_id;
    logic pc_id_assigned;
    
    //Branch Predictor 
    logic [31:0] branch_flush_pc;
    logic [31:0] predicted_pc;
    logic use_prediction;
    logic is_return;
    logic is_call;
    logic is_branch;

    modport branch_predictor (
        input if_pc, if_id, new_mem_request, next_pc, pc_id, pc_id_assigned,
        output branch_flush_pc, predicted_pc, use_prediction, is_return, is_call, is_branch
    );
    modport fetch (
        input branch_flush_pc, predicted_pc, use_prediction, is_return, is_call, is_branch,
        output if_pc, if_id, new_mem_request, next_pc, pc_id, pc_id_assigned
     );

endinterface

interface unit_issue_interface;
    import cva5_types::*;

    logic possible_issue;
    logic new_request;
    id_t id;

    logic ready;

    modport decode (input ready, output possible_issue, new_request, id);
    modport unit (output ready, input possible_issue, new_request, id);
endinterface

interface unit_writeback_interface #(parameter DATA_WIDTH = 32);
    import cva5_types::*;

    //Handshaking
    logic ack;
    logic done;

    id_t id;
    logic [DATA_WIDTH-1:0] rd;

    modport unit (input ack, output done, id, rd);
    modport wb (output ack, input done, id, rd);
endinterface

interface ras_interface;
    logic push;
    logic pop;
    logic branch_fetched;
    logic branch_retired;

    logic [31:0] new_addr;
    logic [31:0] addr;

    modport branch_predictor (output branch_retired);
    modport self (input push, pop, new_addr, branch_fetched, branch_retired, output addr);
    modport fetch (input addr, output pop, push, new_addr, branch_fetched);
endinterface


interface exception_interface;
    import riscv_types::*;
    import cva5_types::*;

    logic valid;
    logic possible;
    
    exception_code_t code;
    logic [31:0] tval;
    logic [31:0] pc;
    logic discard;
    
    modport unit (output valid, possible, code, tval, pc, discard);
    modport econtrol (input valid, possible, code, tval, pc, discard);
endinterface

interface fifo_interface #(parameter type DATA_TYPE = logic);
    logic push;
    logic pop;
    DATA_TYPE data_in;
    DATA_TYPE data_out;
    logic valid;
    logic full;
    logic potential_push;
    modport enqueue (input full, output data_in, push, potential_push);
    modport dequeue (input valid, data_out, output pop);
    modport structure(input push, pop, data_in, potential_push, output data_out, valid, full);
endinterface

interface mmu_interface;
    import csr_types::*;
    
    //From TLB
    logic request;
    logic execute;
    logic rnw;
    logic [31:0] virtual_address;

    //TLB response
    logic write_entry;
    logic superpage;
    pte_perms_t perms;
    logic [19:0] upper_physical_address;
    logic is_fault;

    //From CSR
    logic [21:0] satp_ppn;
    logic mxr; //Make eXecutable Readable
    logic sum; //permit Supervisor User Memory access
    privilege_t privilege;

    modport mmu (input virtual_address, request, execute, rnw, satp_ppn, mxr, sum, privilege, output write_entry, superpage, perms, upper_physical_address, is_fault);
    modport tlb (input write_entry, superpage, perms, upper_physical_address, is_fault, mxr, sum, privilege, output request, virtual_address, execute, rnw);
    modport csr (output satp_ppn, mxr, sum, privilege);

endinterface

interface tlb_interface;
    //Handshaking
    logic ready;
    logic new_request;
    logic done;

    //TLB Inputs
    logic [31:0] virtual_address;
    logic rnw;

    //TLB Outputs
    logic is_fault;
    logic [31:0] physical_address;

    modport tlb (
        input new_request, virtual_address, rnw,
        output ready, done, is_fault, physical_address
    );
    modport requester  (
        output new_request, virtual_address, rnw,
        input ready, done, is_fault, physical_address
    );
endinterface

interface load_store_queue_interface;
    import riscv_types::*;
    import cva5_types::*;

    //Issue inputs
    lsq_entry_t data_in;
    logic potential_push;
    logic push;
    logic load_pop;
    logic store_pop;

    //Address translation
    logic addr_push;
    lsq_addr_entry_t addr_data_in;

    //LSQ outputs
    data_access_shared_inputs_t load_data_out;
    data_access_shared_inputs_t store_data_out;

    logic load_valid;
    logic store_valid;

    logic full;

    //LSQ status
    logic sq_empty;
    logic empty;

    modport queue (
        input data_in, potential_push, push, addr_push, addr_data_in, load_pop, store_pop, 
        output full, load_data_out, store_data_out, load_valid, store_valid, sq_empty, empty
    );
    modport ls (
        output data_in, potential_push, push, addr_push, addr_data_in, load_pop, store_pop,
        input full, load_data_out, store_data_out, load_valid, store_valid, sq_empty, empty
    );
endinterface


interface store_queue_interface;
    import riscv_types::*;
    import cva5_types::*;

    //Issue inputs
    lsq_entry_t data_in;
    logic push;
    logic pop;

    sq_entry_t data_out;
    logic valid;
    logic full;

    //SQ status
    logic empty;

    modport queue (
        input data_in, push, pop,
        output full, data_out, valid, empty
    );
    modport ls (
        output data_in, push, pop,
        input full, data_out, valid, empty
    );
endinterface

interface cache_functions_interface #(parameter int TAG_W = 8, parameter int LINE_W = 4, parameter int SUB_LINE_W = 2);

    function logic [LINE_W-1:0] xor_mask (int WAY);
        for (int i = 0; i < LINE_W; i++)
            xor_mask[i] = ((WAY % 2) == 0) ? 1'b1 : 1'b0;
    endfunction

    function logic [LINE_W-1:0] getHashedLineAddr (logic[31:0] addr, int WAY);
        getHashedLineAddr = addr[2 + SUB_LINE_W +: LINE_W] ^ (addr[2 + SUB_LINE_W + LINE_W +: LINE_W] & xor_mask(WAY));
    endfunction

    function logic[TAG_W-1:0] getTag(logic[31:0] addr);
        getTag = addr[2 + LINE_W + SUB_LINE_W +: TAG_W];
    endfunction

    function logic [LINE_W-1:0] getTagLineAddr (logic[31:0] addr);
        getTagLineAddr = addr[2 + SUB_LINE_W +: LINE_W];
    endfunction

    function logic [LINE_W+SUB_LINE_W-1:0] getDataLineAddr (logic[31:0] addr);
        getDataLineAddr = addr[2 +: LINE_W + SUB_LINE_W];
    endfunction

endinterface

interface addr_utils_interface #(parameter logic [31:0] BASE_ADDR = 32'h00000000, parameter logic [31:0] UPPER_BOUND = 32'hFFFFFFFF);
        //The range should be aligned for performance
        function address_range_check (input logic[31:0] addr);
            /* verilator lint_off UNSIGNED */
            /* verilator lint_off CMPCONST */
            return addr >= BASE_ADDR & addr <= UPPER_BOUND;
            /* verilator lint_on UNSIGNED */
            /* verilator lint_on CMPCONST */
        endfunction
endinterface

interface memory_sub_unit_interface;
    logic new_request;
    logic [31:0] addr;
    logic re;
    logic we;
    logic [3:0] be;
    logic [31:0] data_in;

    logic [31:0] data_out;
    logic data_valid;
    logic ready;

    modport responder (
        input addr, re, we, be, data_in, new_request,
        output data_out, data_valid, ready
    );
    modport controller (
        input data_out, data_valid, ready,
        output addr, re, we, be, data_in, new_request
    );
endinterface

//start and done are cycle cycle pulses
interface unsigned_division_interface #(parameter DATA_WIDTH = 32);
    logic start;
    logic [DATA_WIDTH-1:0] dividend;
    logic [$clog2(DATA_WIDTH)-1:0] dividend_CLZ;
    logic [DATA_WIDTH-1:0] divisor;
    logic [$clog2(DATA_WIDTH)-1:0] divisor_CLZ;
    logic [DATA_WIDTH-1:0] remainder;
    logic [DATA_WIDTH-1:0] quotient;
    logic done;
    logic divisor_is_zero;
    modport requester (input remainder, quotient, done, output dividend, dividend_CLZ, divisor, divisor_CLZ, divisor_is_zero, start);
    modport divider (output remainder, quotient, done, input dividend, dividend_CLZ, divisor, divisor_CLZ, divisor_is_zero, start);
endinterface

interface unsigned_sqrt_interface #(parameter DATA_WIDTH = 32);
    logic start;
    logic [DATA_WIDTH-1:0] radicand;
    logic [DATA_WIDTH-1:0] remainder;
    logic [DATA_WIDTH-1:0] result;
    logic done;

    modport requester (input remainder, result, done, output radicand, start);
    modport sqrt (output remainder, result, done, input radicand, start);
endinterface

interface renamer_interface #(parameter NUM_WB_GROUPS = 3, parameter READ_PORTS = 2);
    import riscv_types::*;
    import cva5_types::*;

    rs_addr_t rd_addr;
    rs_addr_t rs_addr [READ_PORTS];
    logic [$clog2(NUM_WB_GROUPS)-1:0] rd_wb_group;
    logic uses_rd;
    id_t id;

    phys_addr_t phys_rs_addr [READ_PORTS];
    phys_addr_t phys_rd_addr;

    logic [$clog2(NUM_WB_GROUPS)-1:0] rs_wb_group [READ_PORTS];

    modport renamer (
        input rd_addr, rs_addr, rd_wb_group, uses_rd, id,
        output phys_rs_addr, rs_wb_group, phys_rd_addr
    );
    modport decode (
        input phys_rs_addr, rs_wb_group, phys_rd_addr,
        output rd_addr, rs_addr, rd_wb_group, uses_rd, id
    );
endinterface

interface register_file_issue_interface #(parameter NUM_WB_GROUPS = 3, parameter DATA_WIDTH = 32, parameter READ_PORTS = 2);
    import cva5_types::*;

    //read interface
    phys_addr_t phys_rs_addr [READ_PORTS];
    logic [$clog2(NUM_WB_GROUPS)-1:0] rs_wb_group [READ_PORTS];
    logic [DATA_WIDTH-1:0] data [READ_PORTS];
    logic inuse [READ_PORTS];

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

interface fp_intermediate_wb_interface;
    import cva5_types::*;
    import fpu_types::*;

    logic ack;

    id_t id;
    logic done;
    fp_t rd;
    logic expo_overflow;
    fflags_t fflags;
    rm_t rm;
    logic carry;
    logic safe;
    logic hidden;
    grs_t grs;
    fp_shift_amt_t clz;
    logic right_shift;
    fp_shift_amt_t right_shift_amt;
    logic subnormal;
    logic ignore_max_expo;
    logic d2s;

    modport unit (
        input ack,
        output id, done, rd, expo_overflow, fflags, rm, hidden, grs, clz, carry, safe, subnormal, right_shift, right_shift_amt, ignore_max_expo, d2s
    );
    modport wb (
        output ack,
        input id, done, rd, expo_overflow, fflags, rm, hidden, grs, clz, carry, safe, subnormal, right_shift, right_shift_amt, ignore_max_expo, d2s
    );
endinterface

interface amo_interface;
    import riscv_types::*;

    //Atomic Load Reserved and Store Conditional
    logic set_reservation;
    logic clear_reservation;
    logic[31:0] reservation;
    logic reservation_valid;

    //Atomic Read-Modify-Write
    logic rmw_valid;
    amo_t op;
    logic[31:0] rs1;
    logic[31:0] rs2;
    logic[31:0] rd;

    modport subunit (
        input reservation_valid, rd,
        output set_reservation, clear_reservation, reservation, rmw_valid, op, rs1, rs2
    );
    modport amo_unit (
        output reservation_valid, rd,
        input set_reservation, clear_reservation, reservation, rmw_valid, op, rs1, rs2
    );

endinterface
