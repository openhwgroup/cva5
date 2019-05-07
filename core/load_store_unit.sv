/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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

module load_store_unit (
        input logic clk,
        input logic rst,
        input load_store_inputs_t ls_inputs,
        func_unit_ex_interface.unit ls_ex,

        input logic dcache_on,
        input logic clear_reservation,
        tlb_interface.mem tlb,

        input logic gc_flush_LS_input,

        l1_arbiter_request_interface.requester l1_request,
        l1_arbiter_return_interface.requester l1_response,
        input sc_complete,
        input sc_success,

        axi_interface.master m_axi,
        avalon_interface.master m_avalon,
        wishbone_interface.master m_wishbone,

        local_memory_interface.master data_bram,

        output logic store_committed,
        output instruction_id_t store_id,

        output logic load_store_FIFO_emptying,
        output exception_packet_t ls_exception,

        unit_writeback_interface.unit ls_wb
        );

    localparam NUM_SUB_UNITS = USE_D_SCRATCH_MEM+USE_BUS+USE_DCACHE;
    localparam NUM_SUB_UNITS_W = $clog2(NUM_SUB_UNITS);

    localparam BRAM_ID = 0;
    localparam BUS_ID = USE_D_SCRATCH_MEM;
    localparam DCACHE_ID = USE_D_SCRATCH_MEM+USE_BUS;

    //Should be equal to pipeline depth of longest load/store subunit
    localparam ATTRIBUTES_DEPTH = 2;

    typedef enum bit [2:0] {BU = 3'b000, HU = 3'b001, BS = 3'b010, HS = 3'b011, W = 3'b100} sign_type;

    data_access_shared_inputs_t d_inputs;
    ls_sub_unit_interface ls_sub[NUM_SUB_UNITS-1:0]();

    logic units_ready;
    logic issue_request;
    logic data_valid;
    logic load_complete;

    logic [31:0] virtual_address;
    logic [3:0] be, be_from_op;

    logic [31:0] unit_muxed_load_data;
    logic [31:0] aligned_load_data;
    logic [31:0] final_load_data;

    logic [31:0] most_recent_load;
    logic [31:0] forwarded_data;
    logic [31:0] previous_load, previous_load_r;
    logic [31:0] stage1_raw_data;

    logic [31:0] unit_data_array [NUM_SUB_UNITS-1:0];
    logic [NUM_SUB_UNITS-1:0] unit_ready;
    logic [NUM_SUB_UNITS-1:0] unit_data_valid;
    logic [NUM_SUB_UNITS-1:0] last_unit;
    logic [NUM_SUB_UNITS-1:0] current_unit;

    logic unaligned_addr;
    logic [NUM_SUB_UNITS-1:0] sub_unit_address_match;

    logic dcache_forward_data;
    logic [2:0] dcache_stage2_fn3;

    logic [1:0] inflight_count;
    logic unit_stall;


    //AMO support
    //LR -- invalidates line if tag hit
    //SC -- blocks until response
    //AMO ops -- invalidates line if tag hit, forwards old value to writeback and updates value before writing to cache
    logic reservation;
    logic lr;
    logic sc;
    logic is_amo;
    logic [4:0] amo_op;

    typedef struct packed{
        logic [2:0] fn3;
        logic [1:0] byte_addr;
        instruction_id_t instruction_id;
    } load_attributes_t;
    load_attributes_t  load_attributes_in, stage2_attr;
    load_store_inputs_t  stage1;

    //FIFOs
    fifo_interface #(.DATA_WIDTH($bits(load_store_inputs_t))) input_fifo();
    fifo_interface #(.DATA_WIDTH($bits(load_attributes_t))) load_attributes();
    fifo_interface #(.DATA_WIDTH(XLEN)) wb_fifo();
    /////////////////////////////////////////


    /*********************************
     *  Primary control signals
     *********************************/
    always_ff @(posedge clk) begin
        if (rst)
            inflight_count <= 0;
        else if (load_attributes.push & ~ls_wb.accepted)
            inflight_count <= inflight_count + 1;
        else if (~load_attributes.push &  ls_wb.accepted)
            inflight_count <= inflight_count - 1;
    end

    genvar i;
    generate
        for(i=0; i < NUM_SUB_UNITS; i++) begin
            assign unit_ready[i] = ls_sub[i].ready;
            assign unit_data_valid[i] = ls_sub[i].data_valid;
        end
    endgenerate

    assign units_ready = &unit_ready;
    assign data_valid = |unit_data_valid;

    //initial last_unit = 0;//For simulator
    assign current_unit = sub_unit_address_match;
    always_ff @ (posedge clk) begin
        if (rst)
            last_unit <= 0;
        else if (load_attributes.push)
            last_unit <= sub_unit_address_match;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            store_committed <= 0;
        else
            store_committed <= stage1.store & issue_request;
    end

    always_ff @ (posedge clk) begin
            store_id <= stage1.instruction_id;
    end

    //When switching units, ensure no outstanding loads so that there can be no timing collisions with results
    assign unit_stall = (current_unit != last_unit) && ~load_attributes.empty;

    assign issue_request = input_fifo.valid && units_ready && (inflight_count < 2) && ~unit_stall && ~unaligned_addr;
    assign load_complete = data_valid;

    always_ff @ (posedge clk) begin
        assert ((issue_request & |sub_unit_address_match) || (!issue_request)) else $error("invalid L/S address");
    end

    generate if (USE_D_SCRATCH_MEM) begin
            assign sub_unit_address_match[BRAM_ID] = tlb.physical_address[31:32-SCRATCH_BIT_CHECK] == SCRATCH_ADDR_L[31:32-SCRATCH_BIT_CHECK];
            assign ls_sub[BRAM_ID].new_request = sub_unit_address_match[BRAM_ID] & issue_request;
        end
    endgenerate

    generate if (USE_BUS) begin
            assign sub_unit_address_match[BUS_ID] = tlb.physical_address[31:32-BUS_BIT_CHECK] == BUS_ADDR_L[31:32-BUS_BIT_CHECK];
            assign ls_sub[BUS_ID].new_request = sub_unit_address_match[BUS_ID] & issue_request;
        end
    endgenerate

    generate if (USE_DCACHE) begin
            assign sub_unit_address_match[DCACHE_ID] = tlb.physical_address[31:32-MEMORY_BIT_CHECK] == MEMORY_ADDR_L[31:32-MEMORY_BIT_CHECK];
            assign ls_sub[DCACHE_ID].new_request = sub_unit_address_match[DCACHE_ID] & issue_request;
        end
    endgenerate
    /*********************************************/


    /*********************************
     *  Input FIFO
     *********************************/
    taiga_fifo #(.DATA_WIDTH($bits(load_store_inputs_t)), .FIFO_DEPTH(LS_INPUT_BUFFER_DEPTH), .FIFO_TYPE(NON_MUXED_INPUT_FIFO)
        ) ls_input_fifo (.fifo(input_fifo), .rst(rst | gc_flush_LS_input), .*);

    assign input_fifo.data_in = ls_inputs;
    assign input_fifo.push = ls_ex.new_request_dec;
    assign ls_ex.ready = ~input_fifo.full;
    assign input_fifo.pop = issue_request;
    assign load_store_FIFO_emptying = input_fifo.early_empty;
    assign stage1 = input_fifo.data_out;
    /*********************************
     * TLB interface
     *********************************/
    assign virtual_address = stage1.virtual_address;// + 32'(signed'(stage1.offset));

    assign tlb.virtual_address = virtual_address;
    assign tlb.new_request = input_fifo.valid;
    assign tlb.execute = 0;
    assign tlb.rnw = stage1.load & ~stage1.store;
    /*********************************************/

    /*********************************
     * Alignment Exception
     *********************************/
    always_comb begin
        case(stage1.fn3)
            LS_H_fn3 : unaligned_addr = virtual_address[0];
            LS_W_fn3 : unaligned_addr = |virtual_address[1:0];
            default : unaligned_addr = 0;
        endcase
    end
    assign ls_exception.valid = unaligned_addr & input_fifo.valid;
    assign ls_exception.code = stage1.load ? LOAD_ADDR_MISSALIGNED : STORE_AMO_ADDR_MISSALIGNED;
    assign ls_exception.pc = stage1.pc;
    assign ls_exception.tval = stage1.virtual_address;
    assign ls_exception.id = stage1.instruction_id;

    /*********************************************/


    /*********************************
     * Input Processing
     * (byte enables, input muxing)
     *********************************/
    /*Byte enable generation
     * Only set on store
     *   SW: all bytes
     *   SH: upper or lower half of bytes
     *   SB: specific byte
     */
    always_comb begin
        for (int i = 0; i < XLEN/8; i = i+ 1) begin
            case({stage1.store,stage1.fn3[1:0]})
                {1'b1, LS_B_fn3[1:0]} : be[i] = (virtual_address[1:0] == i[1:0]);
                {1'b1, LS_H_fn3[1:0]} : be[i] = (virtual_address[1] == i[1]);
                {1'b1, LS_W_fn3[1:0]} : be[i] = '1;
                default : be[i] = 0;
            endcase
        end
    end


    //AMO identification for dcache
    generate
        if (USE_AMO) begin
            assign lr = stage1.is_amo && (stage1.amo == AMO_LR);
            assign sc = stage1.is_amo && (stage1.amo == AMO_SC);
            assign is_amo = stage1.is_amo & ~(lr | sc);
            assign amo_op = stage1.amo;
        end else begin
            assign lr = 0;
            assign sc = 0;
            assign is_amo = 0;
            assign amo_op = 0;
        end
    endgenerate

    //Shared inputs
    assign d_inputs.addr = tlb.physical_address;
    assign d_inputs.load = stage1.load;
    assign d_inputs.store = stage1.store;
    assign d_inputs.be = be;
    assign d_inputs.fn3 = stage1.fn3;

    logic forward_data;
    assign forward_data = stage1.load_store_forward | dcache_forward_data;
    assign stage1_raw_data =  forward_data ? (load_attributes.valid ? final_load_data : previous_load) : stage1.rs2;

    //Input: ABCD
    //Assuming aligned requests,
    //Possible selections: (A/C/D, B/D, C/D, D)
    logic [1:0] data_in_mux;
    always_comb begin
        data_in_mux = dcache_forward_data ? dcache_stage2_fn3[1:0] : virtual_address[1:0];
        d_inputs.data_in[7:0] = stage1_raw_data[7:0];
        d_inputs.data_in[15:8] = (data_in_mux == 2'b01) ? stage1_raw_data[7:0] : stage1_raw_data[15:8];
        d_inputs.data_in[23:16] = (data_in_mux == 2'b10) ? stage1_raw_data[7:0] : stage1_raw_data[23:16];
        case(data_in_mux)
            2'b10 : d_inputs.data_in[31:24] = stage1_raw_data[15:8];
            2'b11 : d_inputs.data_in[31:24] = stage1_raw_data[7:0];
            default : d_inputs.data_in[31:24] = stage1_raw_data[31:24];
        endcase
    end

    /*********************************
     *  Load attributes FIFO
     *********************************/
    taiga_fifo #(.DATA_WIDTH($bits(load_attributes_t)), .FIFO_DEPTH(ATTRIBUTES_DEPTH), .FIFO_TYPE(LUTRAM_FIFO)
        ) attributes_fifo (.fifo(load_attributes), .*);
    assign load_attributes_in.fn3 = stage1.fn3;
    assign load_attributes_in.byte_addr = virtual_address[1:0];
    assign load_attributes_in.instruction_id = stage1.instruction_id;

    assign load_attributes.data_in = load_attributes_in;

    assign load_attributes.push = issue_request & stage1.load;
    assign load_attributes.pop = load_complete;

    assign stage2_attr  = load_attributes.data_out;

    /*********************************
     *  Unit Instantiation
     *********************************/
    //BRAM
    generate if (USE_D_SCRATCH_MEM)
            dbram d_bram (.clk(clk), .rst(rst), .ls_inputs(d_inputs), .ls(ls_sub[BRAM_ID]), .data_out(unit_data_array[BRAM_ID]), .*);
    endgenerate
    generate
        if (USE_BUS) begin
            if(BUS_TYPE == AXI_BUS)
                axi_master axi_bus (.clk(clk), .rst(rst), .ls_inputs(d_inputs), .size({1'b0,stage1.fn3[1:0]}), .m_axi(m_axi),.ls(ls_sub[BUS_ID]), .data_out(unit_data_array[BUS_ID])); //Lower two bits of fn3 match AXI specification for request size (byte/halfword/word)
            else if (BUS_TYPE == WISHBONE_BUS)
                wishbone_master wishbone_bus (.clk(clk), .rst(rst), .ls_inputs(d_inputs), .m_wishbone(m_wishbone),.ls(ls_sub[BUS_ID]), .data_out(unit_data_array[BUS_ID]));
            else if (BUS_TYPE == AVALON_BUS)  begin
                avalon_master avalon_bus (.clk(clk), .rst(rst), .ls_inputs(d_inputs), .m_avalon(m_avalon),.ls(ls_sub[BUS_ID]), .data_out(unit_data_array[BUS_ID]));
            end
        end
    endgenerate

    //Cache
    generate if (USE_DCACHE)
            dcache data_cache (.clk(clk), .rst(rst), .ls_inputs(d_inputs), .ls(ls_sub[DCACHE_ID]), .is_amo(is_amo), .use_forwarded_data(stage1.load_store_forward), .data_out(unit_data_array[DCACHE_ID]), .*);
    endgenerate
    /*************************************
     * Output Muxing
     *************************************/
    //unit mux
    always_comb begin
        unit_muxed_load_data = 0;
        foreach (unit_data_array[i])
            unit_muxed_load_data |= unit_data_array[i];
    end

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


    /*********************************
     *  Output FIFO
     *********************************/
    localparam LS_OUTPUT_FIFO_DEPTH = 2;
    logic[LS_OUTPUT_FIFO_DEPTH:0] valid_chain;

    always_ff @ (posedge clk) begin
        if (rst) begin
            valid_chain[0] <= 1;
            valid_chain[LS_OUTPUT_FIFO_DEPTH:1] <= 0;
        end
        else begin
            case({load_complete,ls_wb.accepted})
                0 : valid_chain <= valid_chain;
                1 : valid_chain <= {1'b0, valid_chain[LS_OUTPUT_FIFO_DEPTH:1]};
                2 : valid_chain <= {valid_chain[LS_OUTPUT_FIFO_DEPTH-1:0], 1'b0};
                3 : valid_chain <= valid_chain;
            endcase
        end
    end

    always_ff @ (posedge clk) begin
        if (load_complete) begin
            previous_load <= final_load_data;
            previous_load_r <= previous_load;
        end
    end

    assign ls_wb.rd = valid_chain[2] ? previous_load_r : previous_load;

    assign ls_wb.done_next_cycle = load_complete;
    assign ls_wb.instruction_id = stage2_attr.instruction_id;
    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert (~ls_wb.accepted | (ls_wb.accepted & ~valid_chain[0])) else $error("Spurious ack for LS Unit");
    end
endmodule
