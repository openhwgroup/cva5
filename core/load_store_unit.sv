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

        //Early store completion in writeback
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

    //Should be equal to pipeline depth of longest load/store subunit
    localparam ATTRIBUTES_DEPTH = USE_DCACHE ? 2 : 1;

    data_access_shared_inputs_t shared_inputs;
    ls_sub_unit_interface #(.BASE_ADDR(SCRATCH_ADDR_L), .UPPER_BOUND(SCRATCH_ADDR_H), .BIT_CHECK(SCRATCH_BIT_CHECK)) bram();
    ls_sub_unit_interface #(.BASE_ADDR(BUS_ADDR_L), .UPPER_BOUND(BUS_ADDR_H), .BIT_CHECK(BUS_BIT_CHECK)) bus();
    ls_sub_unit_interface #(.BASE_ADDR(MEMORY_ADDR_L), .UPPER_BOUND(MEMORY_ADDR_H), .BIT_CHECK(MEMORY_BIT_CHECK)) cache();

    logic units_ready;
    logic store_ready;
    logic issue_request;
    logic load_complete;

    logic [31:0] prev_load;

    logic [31:0] virtual_address;
    logic [3:0] be;

    logic [31:0] unit_muxed_load_data;
    logic [31:0] aligned_load_data;
    logic [31:0] final_load_data;

    logic [31:0] stage1_raw_data;

    logic [31:0] unit_data_array [NUM_SUB_UNITS-1:0];
    logic [NUM_SUB_UNITS-1:0] unit_ready;
    logic [NUM_SUB_UNITS-1:0] unit_data_valid;
    logic [NUM_SUB_UNITS-1:0] last_unit;
    logic [NUM_SUB_UNITS-1:0] current_unit;

    logic unaligned_addr;
    logic [NUM_SUB_UNITS-1:0] sub_unit_address_match;

    logic unit_stall;

    typedef struct packed{
        logic [31:0] virtual_address;
        logic [31:0] store_data;
        logic [2:0] fn3;
        logic load;
        logic store;
        logic load_store_forward;
        instruction_id_t instruction_id;
        instruction_id_t store_forward_id;
        //exception support
        logic [31:0] pc;
        //amo support
        amo_details_t amo;
    } load_store_input_fifo_t;
    load_store_input_fifo_t fifo_inputs;

    typedef struct packed{
        logic [2:0] fn3;
        logic [1:0] byte_addr;
        instruction_id_t instruction_id;
        logic [0:0] subunit_id;
    } load_attributes_t;
    load_attributes_t  load_attributes_in, stage2_attr;
    load_store_input_fifo_t  stage1;

    //FIFOs
    fifo_interface #(.DATA_WIDTH($bits(load_store_input_fifo_t))) input_fifo();
    fifo_interface #(.DATA_WIDTH($bits(load_attributes_t))) load_attributes();

    ////////////////////////////////////////////////////
    //Implementation
    ////////////////////////////////////////////////////
    //Input FIFO
    taiga_fifo #(.DATA_WIDTH($bits(load_store_input_fifo_t)), .FIFO_DEPTH(MAX_INFLIGHT_COUNT))
        ls_input_fifo (.fifo(input_fifo), .*);

    assign fifo_inputs.virtual_address = ls_inputs.rs1 + 32'(signed'(ls_inputs.offset));
    assign fifo_inputs.store_data = ls_inputs.rs2;
    assign fifo_inputs.fn3 = ls_inputs.fn3;
    assign fifo_inputs.load = ls_inputs.load;
    assign fifo_inputs.store = ls_inputs.store;
    assign fifo_inputs.load_store_forward = ls_inputs.load_store_forward;
    assign fifo_inputs.instruction_id = issue.instruction_id;
    assign fifo_inputs.store_forward_id = ls_inputs.store_forward_id;
    assign fifo_inputs.pc = ls_inputs.pc;
    assign fifo_inputs.amo = ls_inputs.amo;

    assign input_fifo.data_in = fifo_inputs;
    assign input_fifo.push = issue.new_request;
    assign input_fifo.supress_push = gc_fetch_flush;
    assign issue.ready = 1;//As FIFO depth is the same as MAX_INFLIGHT_COUNT
    assign input_fifo.pop = issue_request;
    assign stage1 = input_fifo.data_out;

    ////////////////////////////////////////////////////
    //Unit tracking
    assign current_unit = sub_unit_address_match;
    always_ff @ (posedge clk) begin
        if (load_attributes.push)
            last_unit <= sub_unit_address_match;
    end

    ////////////////////////////////////////////////////
    //Primary Control Signals
    assign units_ready = &unit_ready;
    assign load_complete = |unit_data_valid;

    always_ff @ (posedge clk) begin
        store_done_id <= stage1.instruction_id;
        store_complete <= stage1.store & issue_request;
    end

    //When switching units, ensure no outstanding loads so that there can be no timing collisions with results
    assign unit_stall = (current_unit != last_unit) && load_attributes.valid;
    assign store_ready = stage1.store & ((stage1.load_store_forward & ~load_attributes.valid) | ~stage1.load_store_forward);
    assign issue_request = input_fifo.valid & units_ready & ~unit_stall & ~unaligned_addr & (~stage1.store | store_ready);

    ////////////////////////////////////////////////////
    //TLB interface
    assign virtual_address = stage1.virtual_address;// + 32'(signed'(stage1.offset));

    assign tlb.virtual_address = virtual_address;
    assign tlb.new_request = input_fifo.valid;
    assign tlb.execute = 0;
    assign tlb.rnw = stage1.load & ~stage1.store;

    ////////////////////////////////////////////////////
    //Alignment Exception
    always_comb begin
        case(stage1.fn3)
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
//    assign ls_exception.code = stage1.load ? LOAD_ADDR_MISSALIGNED : STORE_AMO_ADDR_MISSALIGNED;
//    assign ls_exception.pc = stage1.pc;
//    assign ls_exception.tval = stage1.virtual_address;
//    assign ls_exception.id = stage1.instruction_id;


    ////////////////////////////////////////////////////
    //Input Processing

    //Byte enable generation
    //Only set on store
    //  SW: all bytes
    //  SH: upper or lower half of bytes
    //  SB: specific byte
    always_comb begin
        be = 0;
        case(stage1.fn3[1:0])
            LS_B_fn3[1:0] : be[virtual_address[1:0]] = stage1.store;
            LS_H_fn3[1:0] : begin
                be[virtual_address[1:0]] = stage1.store;
                be[{virtual_address[1], 1'b1}] = stage1.store;
            end
            default : be =  {4{stage1.store}};
        endcase
    end

    ////////////////////////////////////////////////////
    //Unit Inputs
    assign shared_inputs.addr = tlb.physical_address;
    assign shared_inputs.load = stage1.load;
    assign shared_inputs.store = stage1.store;
    assign shared_inputs.be = be;
    assign shared_inputs.fn3 = stage1.fn3;

    //Store forwarding
    assign stage1_raw_data = stage1.load_store_forward ? prev_load : stage1.store_data;

    //Input: ABCD
    //Assuming aligned requests,
    //Possible byte selections: (A/C/D, B/D, C/D, D)
    always_comb begin
        shared_inputs.data_in[7:0] = stage1_raw_data[7:0];
        shared_inputs.data_in[15:8] = (virtual_address[1:0] == 2'b01) ? stage1_raw_data[7:0] : stage1_raw_data[15:8];
        shared_inputs.data_in[23:16] = (virtual_address[1:0] == 2'b10) ? stage1_raw_data[7:0] : stage1_raw_data[23:16];
        case(virtual_address[1:0])
            2'b10 : shared_inputs.data_in[31:24] = stage1_raw_data[15:8];
            2'b11 : shared_inputs.data_in[31:24] = stage1_raw_data[7:0];
            default : shared_inputs.data_in[31:24] = stage1_raw_data[31:24];
        endcase
    end

    ////////////////////////////////////////////////////
    //Load attributes FIFO
    one_hot_to_integer #(NUM_SUB_UNITS) hit_way_conv (.*, .one_hot(sub_unit_address_match), .int_out(load_attributes_in.subunit_id));
    taiga_fifo #(.DATA_WIDTH($bits(load_attributes_t)), .FIFO_DEPTH(ATTRIBUTES_DEPTH))
        attributes_fifo (.fifo(load_attributes), .*);
    assign load_attributes_in.fn3 = stage1.fn3;
    assign load_attributes_in.byte_addr = virtual_address[1:0];
    assign load_attributes_in.instruction_id = stage1.instruction_id;

    assign load_attributes.data_in = load_attributes_in;

    assign load_attributes.push = issue_request & stage1.load;
    assign load_attributes.pop = load_complete;
    assign load_attributes.supress_push = 0;

    assign stage2_attr = load_attributes.data_out;

    ////////////////////////////////////////////////////
    //Unit Instantiation
    generate if (USE_D_SCRATCH_MEM) begin
            assign sub_unit_address_match[BRAM_ID] = bram.address_range_check(tlb.physical_address);
            assign bram.new_request = sub_unit_address_match[BRAM_ID] & issue_request;

            assign unit_ready[BRAM_ID] = bram.ready;
            assign unit_data_valid[BRAM_ID] = bram.data_valid;

            dbram d_bram (.*, .ls_inputs(shared_inputs), .ls(bram), .data_out(unit_data_array[BRAM_ID]));
        end
    endgenerate

    generate if (USE_BUS) begin
            assign sub_unit_address_match[BUS_ID] = bus.address_range_check(tlb.physical_address);
            assign bus.new_request = sub_unit_address_match[BUS_ID] & issue_request;

            assign unit_ready[BUS_ID] = bus.ready;
            assign unit_data_valid[BUS_ID] = bus.data_valid;

            if(BUS_TYPE == AXI_BUS)
                axi_master axi_bus (.*, .ls_inputs(shared_inputs), .size({1'b0,stage1.fn3[1:0]}), .m_axi(m_axi), .ls(bus), .data_out(unit_data_array[BUS_ID])); //Lower two bits of fn3 match AXI specification for request size (byte/halfword/word)
            else if (BUS_TYPE == WISHBONE_BUS)
                wishbone_master wishbone_bus (.*, .ls_inputs(shared_inputs), .m_wishbone(m_wishbone), .ls(bus), .data_out(unit_data_array[BUS_ID]));
            else if (BUS_TYPE == AVALON_BUS)  begin
                avalon_master avalon_bus (.*, .ls_inputs(shared_inputs), .m_avalon(m_avalon), .ls(bus), .data_out(unit_data_array[BUS_ID]));
            end
        end
    endgenerate

    generate if (USE_DCACHE) begin
            assign sub_unit_address_match[DCACHE_ID] = cache.address_range_check(tlb.physical_address);
            assign cache.new_request = sub_unit_address_match[DCACHE_ID] & issue_request;

            assign unit_ready[DCACHE_ID] = cache.ready;
            assign unit_data_valid[DCACHE_ID] = cache.data_valid;

            dcache data_cache (.*, .ls_inputs(shared_inputs), .ls(cache), .amo(stage1.amo), .data_out(unit_data_array[DCACHE_ID]));
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

    always_ff @ (posedge clk) begin
        if (load_complete)
            prev_load <= final_load_data;
    end

    ////////////////////////////////////////////////////
    //Output bank
    assign wb.rd = ls_done ? final_load_data : csr_rd;

    logic exception_complete;
    logic ls_done;
    always_ff @ (posedge clk) begin
        exception_complete <= (input_fifo.valid & ls_exception_valid & stage1.load);
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
