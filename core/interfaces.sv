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

interface unit_writeback_interface;
    import riscv_types::*;
    import cva5_types::*;

        logic ack;

        id_t id;
        logic done;
        logic [XLEN-1:0] rd;

        modport unit (
            input ack,
            output id, done, rd
        );
        modport wb (
            output ack,
            input id, done, rd
        );
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
    logic ack;
    
    exception_code_t code;
    id_t id;
    logic [31:0] tval;
    
    modport unit (output valid, code, id, tval, input ack);
    modport econtrol (input valid, code, id, tval, output ack);
endinterface

interface csr_exception_interface;
    import riscv_types::*;
    import cva5_types::*;

    logic valid;
    exception_code_t code;
    logic [31:0] tval;
    logic [31:0] exception_pc;
    logic [31:0] trap_pc;

    modport econtrol (output valid, code, tval, exception_pc, input trap_pc);
    modport csr (input valid, code, tval, exception_pc, output trap_pc);
endinterface

interface fifo_interface #(parameter DATA_WIDTH = 42);//#(parameter type data_type = logic[31:0]);
    logic push;
    logic pop;
    logic [DATA_WIDTH-1:0] data_in;
    logic [DATA_WIDTH-1:0] data_out;
    logic valid;
    logic full;
    logic potential_push;
    modport enqueue (input full, output data_in, push, potential_push);
    modport dequeue (input valid, data_out, output pop);
    modport structure(input push, pop, data_in, potential_push, output data_out, valid, full);
endinterface

interface mmu_interface;
    //From TLB
    logic request;
    logic execute;
    logic rnw;
    logic [31:0] virtual_address;

    //TLB response
    logic write_entry;
    logic [19:0] upper_physical_address;
    logic is_fault;

    //From CSR
    logic [21:0] satp_ppn;
    logic mxr; //Make eXecutable Readable
    logic sum; //permit Supervisor User Memory access
    logic [1:0] privilege;

    modport mmu (input virtual_address, request, execute, rnw, satp_ppn, mxr, sum, privilege, output write_entry, upper_physical_address, is_fault);
    modport tlb (input write_entry, upper_physical_address, is_fault, output request, virtual_address, execute, rnw);
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
    logic execute;

    //TLB Outputs
    logic is_fault;
    logic [31:0] physical_address;

    modport tlb (
        input new_request, virtual_address, rnw, execute,
        output ready, done, is_fault, physical_address
    );
    modport requester  (
        output new_request, virtual_address, rnw, execute,
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
    logic full;

    //LSQ outputs
    data_access_shared_inputs_t data_out;
    logic valid;
    logic pop;

    //LSQ status
    logic sq_empty;
    logic empty;
    logic no_released_stores_pending;

    modport queue (
        input data_in, potential_push, push, pop,
        output full, data_out, valid, sq_empty, empty, no_released_stores_pending
    );
    modport ls (
        output data_in, potential_push, push, pop,
        input full, data_out, valid, sq_empty, empty, no_released_stores_pending
    );
endinterface


interface store_queue_interface;
    import riscv_types::*;
    import cva5_types::*;

    //Issue inputs
    lsq_entry_t data_in;
    logic push;
    logic full;

    sq_entry_t data_out;

    logic valid;
    logic pop;

    //SQ status
    logic empty;
    logic no_released_stores_pending;

    modport queue (
        input data_in, push, pop,
        output full, data_out, valid, empty, no_released_stores_pending
    );
    modport ls (
        output data_in, push, pop,
        input full, data_out, valid, empty, no_released_stores_pending
    );
endinterface

interface writeback_store_interface;
    import riscv_types::*;
    import cva5_types::*;

        id_t id_needed;
        logic possibly_waiting;
        logic waiting;
        logic ack;

        logic id_done;
        logic [31:0] data;

        modport ls (
            input id_done, data,
            output id_needed, possibly_waiting ,waiting, ack
        );
        modport wb (
            input id_needed, possibly_waiting, waiting, ack,
            output id_done, data
        );
endinterface

interface addr_utils_interface #(parameter bit [31:0] BASE_ADDR = 32'h00000000, parameter bit [31:0] UPPER_BOUND = 32'hFFFFFFFF);
        //Based on the lower and upper address ranges,
        //find the number of bits needed to uniquely identify this memory range.
        //Assumption: address range is aligned to its size
        function int unsigned bit_range ();
            for(int i=0; i < 32; i++) begin
                if (BASE_ADDR[i] == UPPER_BOUND[i])
                    return (32 - i);
            end
            return 0;
        endfunction

        localparam int unsigned BIT_RANGE = bit_range();

        function address_range_check (input logic[31:0] addr);
            return (BIT_RANGE == 0) ? 1 : (addr[31:32-BIT_RANGE] == BASE_ADDR[31:32-BIT_RANGE]);
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

interface renamer_interface #(parameter NUM_WB_GROUPS = 2);
    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    rs_addr_t rd_addr;
    rs_addr_t rs_addr [REGFILE_READ_PORTS];
    logic [$clog2(NUM_WB_GROUPS)-1:0] rd_wb_group;
    logic uses_rd;
    id_t id;

    phys_addr_t phys_rs_addr [REGFILE_READ_PORTS];
    phys_addr_t phys_rd_addr;

    logic [$clog2(NUM_WB_GROUPS)-1:0] rs_wb_group [REGFILE_READ_PORTS];

    modport renamer (
        input rd_addr, rs_addr, rd_wb_group, uses_rd, id,
        output phys_rs_addr, rs_wb_group, phys_rd_addr
    );
    modport decode (
        input phys_rs_addr, rs_wb_group, phys_rd_addr,
        output rd_addr, rs_addr, rd_wb_group, uses_rd, id
    );
endinterface

interface register_file_issue_interface #(parameter NUM_WB_GROUPS = 2);
    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    //read interface
    phys_addr_t phys_rs_addr [REGFILE_READ_PORTS];
    logic [$clog2(NUM_WB_GROUPS)-1:0] rs_wb_group [REGFILE_READ_PORTS];
    logic [31:0] data [REGFILE_READ_PORTS];
    logic inuse [REGFILE_READ_PORTS];

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
