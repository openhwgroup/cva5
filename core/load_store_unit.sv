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

import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module load_store_unit (
        input logic clk,
        input logic rst,
        input load_store_inputs_t ls_inputs,
        unit_issue_interface.unit issue,

        input logic dcache_on,
        input logic clear_reservation,
        tlb_interface.mem tlb,

        input logic gc_fetch_flush,
        input logic gc_issue_flush,

        l1_arbiter_request_interface.master l1_request,
        l1_arbiter_return_interface.master l1_response,
        input sc_complete,
        input sc_success,

        axi_interface.master m_axi,
        avalon_interface.master m_avalon,
        wishbone_interface.master m_wishbone,

        local_memory_interface.master data_bram,

        //Store-Writeback Interface
        input instruction_id_t oldest_id,
        input logic [31:0] writeback_data,
        input logic writeback_valid,
        output instruction_id_t store_done_id,
        output logic store_complete,

        input logic[31:0] csr_rd,
        input instruction_id_t csr_id,
        input logic csr_done,

        output exception_packet_t ls_exception,
        output logic ls_exception_valid,

        output unit_writeback_t wb
        );

    localparam NUM_SUB_UNITS = USE_D_SCRATCH_MEM+USE_BUS+USE_DCACHE;
    localparam NUM_SUB_UNITS_W = (NUM_SUB_UNITS == 1) ? 1 : $clog2(NUM_SUB_UNITS);

    localparam BRAM_ID = 0;
    localparam BUS_ID = USE_D_SCRATCH_MEM;
    localparam DCACHE_ID = USE_D_SCRATCH_MEM+USE_BUS;

    //Should be equal to pipeline depth of longest load/store subunit + 1 (for changing between subunits)
    localparam ATTRIBUTES_DEPTH = USE_DCACHE ? 3 : 2;

    data_access_shared_inputs_t shared_inputs;
    ls_sub_unit_interface #(.BASE_ADDR(SCRATCH_ADDR_L), .UPPER_BOUND(SCRATCH_ADDR_H), .BIT_CHECK(SCRATCH_BIT_CHECK)) bram();
    ls_sub_unit_interface #(.BASE_ADDR(BUS_ADDR_L), .UPPER_BOUND(BUS_ADDR_H), .BIT_CHECK(BUS_BIT_CHECK)) bus();
    ls_sub_unit_interface #(.BASE_ADDR(MEMORY_ADDR_L), .UPPER_BOUND(MEMORY_ADDR_H), .BIT_CHECK(MEMORY_BIT_CHECK)) cache();

    logic units_ready;
    logic unit_switch_stall;
    logic ready_for_store;
    logic ready_for_load;
    logic issue_request;
    logic load_complete;

    logic use_store_buffer;

    logic [31:0] virtual_address;

    logic [31:0] unit_muxed_load_data;
    logic [31:0] aligned_load_data;
    logic [31:0] final_load_data;


    logic [31:0] unit_data_array [NUM_SUB_UNITS-1:0];
    logic [NUM_SUB_UNITS-1:0] unit_ready;
    logic [NUM_SUB_UNITS-1:0] unit_data_valid;
    logic [NUM_SUB_UNITS-1:0] last_unit;
    logic [NUM_SUB_UNITS-1:0] current_unit;

    logic unaligned_addr;
    logic [NUM_SUB_UNITS-1:0] sub_unit_address_match;

    logic unit_stall;

    typedef struct packed{
        logic [2:0] fn3;
        logic [1:0] byte_addr;
        instruction_id_t instruction_id;
        logic [NUM_SUB_UNITS_W-1:0] subunit_id;
    } load_attributes_t;
    load_attributes_t  load_attributes_in, stage2_attr;

    //FIFOs
    fifo_interface #(.DATA_WIDTH($bits(load_attributes_t))) load_attributes();

    store_buffer_request_interface sb_request();
    store_buffer_output_interface sb_output();

    logic [31:0] compare_addr;
    logic compare;
    logic address_conflict;

    ////////////////////////////////////////////////////
    //Implementation
    ////////////////////////////////////////////////////


    ////////////////////////////////////////////////////
    //Unit tracking
    assign current_unit = sub_unit_address_match;

    initial last_unit = BRAM_ID;
    always_ff @ (posedge clk) begin
        if (load_attributes.push)
            last_unit <= sub_unit_address_match;
    end


    ////////////////////////////////////////////////////
    //Store buffer
    assign sb_request.addr = tlb.physical_address;
    assign sb_request.fn3 = ls_inputs.fn3;
    assign sb_request.data = ls_inputs.rs2;
    assign sb_request.data_valid = ~ls_inputs.forwarded_store;
    assign sb_request.data_id = ls_inputs.store_forward_id;
    assign sb_request.valid = issue.new_request & ls_inputs.store;
    assign sb_request.id = issue.instruction_id;

    assign sb_output.accepted = use_store_buffer & units_ready;

    store_buffer sb (.*);
    assign compare_addr = virtual_address;
    assign compare = ls_inputs.load;

    assign store_done_id = sb_output.id;
    assign store_complete = sb_output.accepted;
    ////////////////////////////////////////////////////
    //Primary Control Signals
    assign units_ready = &unit_ready;
    assign load_complete = |unit_data_valid;

    assign use_store_buffer = sb_output.valid;

    assign ready_for_load = ls_inputs.load & (~address_conflict) & (~unit_switch_stall) & units_ready & (~sb_output.valid);
    assign ready_for_store = ls_inputs.store & sb_request.ready;

    assign issue.ready = (ready_for_load | ready_for_store);

    always_ff @ (posedge clk) begin
        if (rst)
            unit_switch_stall <= 0;
        else if (issue_request && (current_unit != last_unit) && load_attributes.valid)
            unit_switch_stall <= 1;
        else if (!load_attributes.valid)
            unit_switch_stall <= 0;
    end

    //When switching units, ensure no outstanding loads so that there can be no timing collisions with results
    assign unit_stall = (current_unit != last_unit) && load_attributes.valid;
    assign issue_request = issue.new_request | sb_output.accepted;

    ////////////////////////////////////////////////////
    //TLB interface
    assign virtual_address = ls_inputs.rs1 + 32'(signed'(ls_inputs.offset));

    assign tlb.virtual_address = virtual_address;
    assign tlb.new_request = issue_request;
    assign tlb.execute = 0;
    assign tlb.rnw = ls_inputs.load & ~ls_inputs.store;

    ////////////////////////////////////////////////////
    //Alignment Exception
    always_comb begin
        case(ls_inputs.fn3)
            LS_H_fn3 : unaligned_addr = virtual_address[0];
            LS_W_fn3 : unaligned_addr = |virtual_address[1:0];
            default : unaligned_addr = 0;
        endcase
    end

    assign ls_exception_valid = 0;
//    always_ff @ (posedge clk) begin
//        if (rst | gc_issue_flush)
//            ls_exception_valid <= 0;
//        else if (unaligned_addr & input_fifo.valid)
//            ls_exception_valid <= 0;
//    end
//    assign ls_exception.code = ls_inputs.load ? LOAD_ADDR_MISSALIGNED : STORE_AMO_ADDR_MISSALIGNED;
//    assign ls_exception.pc = ls_inputs.pc;
//    assign ls_exception.tval = ls_inputs.virtual_address;
//    assign ls_exception.id = issue.instruction_id;

    ////////////////////////////////////////////////////
    //Unit Inputs
    assign shared_inputs.addr = use_store_buffer ? sb_output.addr : virtual_address;
    assign shared_inputs.load = ~use_store_buffer;
    assign shared_inputs.store = use_store_buffer;
    assign shared_inputs.be = use_store_buffer ? sb_output.be : 0;
    assign shared_inputs.fn3 = use_store_buffer ? sb_output.fn3 : ls_inputs.fn3;
    assign shared_inputs.data_in = sb_output.data;

    ////////////////////////////////////////////////////
    //Load attributes FIFO
    one_hot_to_integer #(NUM_SUB_UNITS) hit_way_conv (.*, .one_hot(sub_unit_address_match), .int_out(load_attributes_in.subunit_id));
    taiga_fifo #(.DATA_WIDTH($bits(load_attributes_t)), .FIFO_DEPTH(ATTRIBUTES_DEPTH))
        attributes_fifo (.fifo(load_attributes), .*);
    assign load_attributes_in.fn3 = ls_inputs.fn3;
    assign load_attributes_in.byte_addr = virtual_address[1:0];
    assign load_attributes_in.instruction_id = issue.instruction_id;

    assign load_attributes.data_in = load_attributes_in;

    assign load_attributes.push = issue_request & ~use_store_buffer;
    assign load_attributes.pop = load_complete;
    assign load_attributes.supress_push = 0;

    assign stage2_attr = load_attributes.data_out;

    ////////////////////////////////////////////////////
    //Unit Instantiation
    generate if (USE_D_SCRATCH_MEM) begin
            assign sub_unit_address_match[BRAM_ID] = bram.address_range_check(shared_inputs.addr);
            assign bram.new_request = sub_unit_address_match[BRAM_ID] & issue_request;

            assign unit_ready[BRAM_ID] = bram.ready;
            assign unit_data_valid[BRAM_ID] = bram.data_valid;

            dbram d_bram (.*, .ls_inputs(shared_inputs), .ls(bram), .data_out(unit_data_array[BRAM_ID]));
        end
    endgenerate

    generate if (USE_BUS) begin
            assign sub_unit_address_match[BUS_ID] = bus.address_range_check(shared_inputs.addr);
            assign bus.new_request = sub_unit_address_match[BUS_ID] & issue_request;

            assign unit_ready[BUS_ID] = bus.ready;
            assign unit_data_valid[BUS_ID] = bus.data_valid;

            if(BUS_TYPE == AXI_BUS)
                axi_master axi_bus (.*, .ls_inputs(shared_inputs), .size({1'b0,shared_inputs.fn3[1:0]}), .m_axi(m_axi), .ls(bus), .data_out(unit_data_array[BUS_ID])); //Lower two bits of fn3 match AXI specification for request size (byte/halfword/word)
            else if (BUS_TYPE == WISHBONE_BUS)
                wishbone_master wishbone_bus (.*, .ls_inputs(shared_inputs), .m_wishbone(m_wishbone), .ls(bus), .data_out(unit_data_array[BUS_ID]));
            else if (BUS_TYPE == AVALON_BUS)  begin
                avalon_master avalon_bus (.*, .ls_inputs(shared_inputs), .m_avalon(m_avalon), .ls(bus), .data_out(unit_data_array[BUS_ID]));
            end
        end
    endgenerate

    generate if (USE_DCACHE) begin
            assign sub_unit_address_match[DCACHE_ID] = cache.address_range_check(shared_inputs.addr);
            assign cache.new_request = sub_unit_address_match[DCACHE_ID] & issue_request;

            assign unit_ready[DCACHE_ID] = cache.ready;
            assign unit_data_valid[DCACHE_ID] = cache.data_valid;

            dcache data_cache (.*, .ls_inputs(shared_inputs), .ls(cache), .amo(ls_inputs.amo), .data_out(unit_data_array[DCACHE_ID]));
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Output Muxing
    assign unit_muxed_load_data = unit_data_array[stage2_attr.subunit_id];

    //Byte/halfword select: assumes aligned operations
    always_comb begin
        aligned_load_data[31:16] = unit_muxed_load_data[31:16];
        aligned_load_data[15:0] = stage2_attr.byte_addr[1] ? unit_muxed_load_data[31:16] : unit_muxed_load_data[15:0];
        //select halfword first then byte
        aligned_load_data[7:0] = stage2_attr.byte_addr[0] ? aligned_load_data[15:8] : aligned_load_data[7:0];
    end

    //Sign extending
    always_comb begin
        case(stage2_attr.fn3)
            LS_B_fn3 : final_load_data = 32'(signed'(aligned_load_data[7:0]));
            LS_H_fn3 : final_load_data = 32'(signed'(aligned_load_data[15:0]));
            LS_W_fn3 : final_load_data = aligned_load_data;
                //unused 011
            L_BU_fn3 : final_load_data = 32'(unsigned'(aligned_load_data[7:0]));
            L_HU_fn3 : final_load_data = 32'(unsigned'(aligned_load_data[15:0]));
                //unused 110
                //unused 111
            default : final_load_data = aligned_load_data;
        endcase
    end

    ////////////////////////////////////////////////////
    //Output bank
    assign wb.rd = ls_done ? final_load_data : csr_rd;

    logic exception_complete;
    logic ls_done;
    always_ff @ (posedge clk) begin
        exception_complete <= (issue_request & ls_exception_valid & ls_inputs.load);
    end
    assign ls_done = load_complete | exception_complete;

    assign wb.done = csr_done | ls_done;
    assign wb.id = csr_done ? csr_id : stage2_attr.instruction_id;
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert ((issue_request & |sub_unit_address_match) || (!issue_request)) else $error("invalid L/S address");
    end

endmodule
