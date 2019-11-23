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

import taiga_config::*;
import taiga_types::*;
import l2_config_and_types::*;

interface branch_predictor_interface;
    //Fetch signals
    logic [31:0] if_pc;
    logic new_mem_request;
    logic [31:0] next_pc;
    
    //Branch Predictor 
    logic [31:0] branch_flush_pc;
    logic [31:0] predicted_pc;
    logic use_prediction;
    logic [BRANCH_PREDICTOR_WAYS-1:0] update_way;
    logic use_ras;
    branch_predictor_metadata_t metadata;

    modport branch_predictor (
        input if_pc, new_mem_request, next_pc,
        output branch_flush_pc, predicted_pc, use_prediction, update_way, use_ras, metadata
    );
    modport fetch (
        input branch_flush_pc, predicted_pc, use_prediction, update_way, use_ras, metadata,
        output if_pc, new_mem_request, next_pc
     );

endinterface

interface unit_issue_interface;
    logic possible_issue;
    logic new_request;
    logic new_request_r;
    instruction_id_t instruction_id;

    logic ready;

    modport decode (input ready, output possible_issue, new_request, new_request_r, instruction_id);
    modport unit (output ready, input possible_issue, new_request, new_request_r, instruction_id);
endinterface

interface ras_interface;
    logic push;
    logic pop;
    logic [31:0] new_addr;
    logic [31:0] addr;
    logic valid;

    modport branch_unit (output push, pop, new_addr);
    modport self (input push, pop, new_addr, output addr, valid);
    modport fetch (input addr, valid);
endinterface

interface csr_exception_interface;
    logic valid;
    exception_code_t code;
    logic [31:0] pc;
    logic [31:0] addr;

    logic illegal_instruction; //invalid CSR, invalid CSR op, or priviledge
    logic[31:0] csr_pc;

    modport csr (input valid, code, pc, addr, output illegal_instruction, csr_pc);
    modport econtrol (output valid, code, pc, addr, input illegal_instruction, csr_pc);

endinterface

interface exception_interface;
    logic valid;
    logic ack;
    
    exception_code_t code;
    logic [31:0] pc;
    logic [31:0] addr;
    instruction_id_t id;

    modport econtrol (output valid, code, pc, addr, id, input ack);
    modport unit (input valid, code, pc, addr, id, output ack);
endinterface

interface register_file_decode_interface;
    logic[4:0] future_rd_addr; //if not a storing instruction required to be zero
    logic[4:0] rs1_addr;
    logic[XLEN-1:0] rs1_data;
    logic[4:0] rs2_addr; //if not used required to be zero
    logic[XLEN-1:0] rs2_data;
    instruction_id_t id;

    logic uses_rs1;
    logic uses_rs2;
    logic rs1_conflict;
    logic rs2_conflict;
    instruction_id_t rs2_id;
    logic instruction_issued;

    modport decode (output future_rd_addr, rs1_addr, rs2_addr, instruction_issued, id, uses_rs1, uses_rs2, input rs1_conflict, rs2_conflict, rs1_data, rs2_data, rs2_id);
    modport unit (input future_rd_addr, rs1_addr, rs2_addr, instruction_issued, id, uses_rs1, uses_rs2, output rs1_conflict, rs2_conflict, rs1_data, rs2_data, rs2_id);
endinterface


interface register_file_writeback_interface;
    logic[4:0] rd_addr;
    logic retiring;
    logic rd_nzero;

    logic[XLEN-1:0] rd_data;
    instruction_id_t id;

    instruction_id_t rs1_id;
    instruction_id_t rs2_id;

    logic[XLEN-1:0] rs1_data;
    logic[XLEN-1:0] rs2_data;
    logic rs1_valid;
    logic rs2_valid;
    
    modport writeback (output rd_addr, retiring, rd_nzero, rd_data, id, rs1_data, rs2_data, rs1_valid, rs2_valid,  input rs1_id, rs2_id);
    modport unit (input rd_addr, retiring, rd_nzero, rd_data, id, rs1_data, rs2_data, rs1_valid, rs2_valid, output rs1_id, rs2_id);

endinterface


interface tracking_interface;
    instruction_id_t issue_id;
    logic id_available;
    
    inflight_instruction_packet inflight_packet;
    logic issued;
    logic [WB_UNITS_WIDTH-1:0] issue_unit_id;

    modport decode (input issue_id, id_available, output inflight_packet, issued, issue_unit_id);
    modport wb (output issue_id, id_available, input inflight_packet, issued, issue_unit_id);
endinterface

interface fifo_interface #(parameter DATA_WIDTH = 42);//#(parameter type data_type = logic[31:0]);
    logic push;
    logic pop;
    logic [DATA_WIDTH-1:0] data_in;
    logic [DATA_WIDTH-1:0] data_out;
    logic valid;
    logic full;
    logic supress_push;
    modport enqueue (input full, output data_in, push, supress_push);
    modport dequeue (input valid, data_out, output pop);
    modport structure(input push, pop, data_in, supress_push, output data_out, valid, full);
endinterface

interface mmu_interface;
    //From TLB
    logic new_request;
    logic execute;
    logic rnw;
    logic [31:0] virtual_address;

    //TLB response
    logic write_entry;
    logic [19:0] new_phys_addr;

    //From CSR
    logic [21:0] ppn;
    logic mxr; //Make eXecutable Readable
    logic pum; //Protect User Memory
    logic [1:0] privilege;

    modport mmu (input virtual_address, new_request, execute, rnw, ppn, mxr, pum, privilege, output write_entry, new_phys_addr);
    modport tlb (input write_entry, new_phys_addr, output new_request, virtual_address, execute, rnw);
    modport csr (output ppn, mxr, pum, privilege);

endinterface

interface tlb_interface;
    logic [31:0] virtual_address;
    logic new_request;
    logic rnw;
    logic execute;

    logic complete;
    logic [31:0] physical_address;

    logic flush;
    logic flush_complete;

    modport tlb (input virtual_address, new_request, flush, rnw, execute,   output complete, physical_address, flush_complete);
    modport mem  (output new_request, virtual_address, rnw, execute, input complete, physical_address);
    modport fence (output flush, input flush_complete);

endinterface


interface ls_sub_unit_interface #(parameter BASE_ADDR = 32'h00000000, parameter UPPER_BOUND = 32'hFFFFFFFF, parameter BIT_CHECK = 4);
    logic data_valid;
    logic ready;
    logic new_request;

    function  address_range_check (input logic[31:0] addr);
        return (addr[31:32-BIT_CHECK] == BASE_ADDR[31:32-BIT_CHECK]);
    endfunction

    modport sub_unit (input new_request, output data_valid, ready);
    modport ls (output new_request, input data_valid, ready);

endinterface


interface fetch_sub_unit_interface;
    logic [31:0] stage1_addr;
    logic [31:0] stage2_addr;

    logic [31:0] data_out;
    logic data_valid;
    logic ready;
    logic new_request;
    logic flush;

    modport sub_unit (input stage1_addr, stage2_addr,  new_request, flush, output data_out, data_valid, ready);
    modport fetch (output stage1_addr, stage2_addr,  new_request, flush, input data_out, data_valid, ready);

endinterface

//start and done are cycle cycle pulses
interface unsigned_division_interface #(parameter DATA_WIDTH = 32);
    logic start;
    logic [DATA_WIDTH-1:0] dividend;
    logic [DATA_WIDTH-1:0] divisor;
    logic [DATA_WIDTH-1:0] remainder;
    logic [DATA_WIDTH-1:0] quotient;
    logic done;
    logic divisor_is_zero;
    modport requester (input remainder, quotient, done, divisor_is_zero, output dividend, divisor, start);
    modport divider (output remainder, quotient, done, divisor_is_zero, input dividend, divisor, start);
endinterface

//Unit sets the ID of the instruction that will provide the data
//data_valid is high when the data is valid
interface post_issue_forwarding_interface;
    instruction_id_t id;

    logic [31:0] data;
    logic data_valid;

    modport unit (input data, data_valid, output id);
    modport wb (output data, data_valid, input id);
endinterface

