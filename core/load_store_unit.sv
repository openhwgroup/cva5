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

        l1_arbiter_request_interface.requester l1_request,
        l1_arbiter_return_interface.requester l1_response,
        input sc_complete,
        input sc_success,

        axi_interface.master m_axi,
        avalon_interface.master m_avalon,

        bram_interface.user data_bram,

        output logic inorder,
        unit_writeback_interface.unit ls_wb
        );

    localparam NUM_SUB_UNITS = 3;
    localparam NUM_SUB_UNITS_W = $clog2(NUM_SUB_UNITS);

    localparam BRAM_ID = 0;
    localparam BUS_ID = 1;
    localparam DCACHE_ID = 2;

    //Should be equal to pipeline depth of longest load/store subunit
    localparam ATTRIBUTES_DEPTH = 4;

    typedef enum bit [2:0] {BU = 3'b000, HU = 3'b001, BS = 3'b010, HS = 3'b011, W = 3'b100} sign_type;

    data_access_shared_inputs_t d_inputs;
    ls_sub_unit_interface ls_sub[NUM_SUB_UNITS-1:0]();

    logic issue_request;
    logic data_valid;
    logic load_complete;

    logic [31:0] virtual_address;
    logic [3:0]be;

    logic [31:0] unit_muxed_load_data;
    logic [31:0] aligned_load_data;
    logic [31:0] final_load_data;

    logic [31:0] rs2_muxed;
    logic [31:0] most_recent_load;
    logic [31:0] forwarded_data;
    logic [31:0] previous_load;
    logic [31:0] stage1_raw_data;

    logic unaligned_addr;
    logic bus_access;
    logic bram_access;
    logic cache_access;

    logic [31:0] unit_data_array [NUM_SUB_UNITS-1:0];

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
        logic[1:0] unit_id;
        logic [2:0] fn3;
        logic[1:0] byte_addr;
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
    assign issue_request =   ((stage1.load_store_forward & (data_valid | ~load_attributes.valid)) | (~stage1.load_store_forward)) & input_fifo.valid & ls_sub[DCACHE_ID].ready & ls_sub[BRAM_ID].ready & ls_sub[BUS_ID].ready;
    assign data_valid = ls_sub[DCACHE_ID].data_valid | ls_sub[BRAM_ID].data_valid | ls_sub[BUS_ID].data_valid;
    assign load_complete = data_valid & ~wb_fifo.full;

    assign bram_access = tlb.physical_address[31:32-SCRATCH_BIT_CHECK] == SCRATCH_ADDR_L[31:32-SCRATCH_BIT_CHECK];
    assign bus_access = tlb.physical_address[31:32-BUS_BIT_CHECK] == BUS_ADDR_L[31:32-BUS_BIT_CHECK];
    assign cache_access = tlb.physical_address[31:32-MEMORY_BIT_CHECK] == MEMORY_ADDR_L[31:32-MEMORY_BIT_CHECK];

    assign ls_sub[BRAM_ID].new_request = bram_access & issue_request;
    assign ls_sub[BUS_ID].new_request = bus_access & issue_request;
    assign ls_sub[DCACHE_ID].new_request = cache_access & issue_request;

    assign ls_sub[BRAM_ID].ack = ls_sub[BRAM_ID].data_valid & ~wb_fifo.full;
    assign ls_sub[BUS_ID].ack = ls_sub[BUS_ID].data_valid & ~wb_fifo.full;
    assign ls_sub[DCACHE_ID].ack = ls_sub[DCACHE_ID].data_valid & ~wb_fifo.full;
    /*********************************************/


    /*********************************
     *  Input FIFO
     *********************************/
    lutram_fifo #(.DATA_WIDTH($bits(load_store_inputs_t)), .FIFO_DEPTH(LS_INPUT_BUFFER_DEPTH)) ls_input_fifo (.fifo(input_fifo), .*);

    assign input_fifo.data_in = ls_inputs;
    assign input_fifo.push = ls_ex.new_request_dec;
    assign ls_ex.ready = ~input_fifo.full;
    assign input_fifo.pop = issue_request;
    assign inorder = input_fifo.valid;
    assign stage1 = input_fifo.data_out;
    /*********************************
     * TLB interface
     *********************************/
    assign virtual_address = stage1.virtual_address + 32'(signed'(stage1.offset));

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
        for (integer i = 0; i < XLEN/8; i = i+ 1) begin
            be[i] = stage1.store && (
                    ((stage1.fn3 == LS_W_fn3)) ||
                    ((stage1.fn3 == LS_H_fn3) && (virtual_address[1] == i[1])) ||
                    ((stage1.fn3 == LS_B_fn3) && (virtual_address[1:0] == i)));
        end
    end

    assign most_recent_load = data_valid ? final_load_data : previous_load;
    assign stage1_raw_data = stage1.load_store_forward ? most_recent_load : stage1.rs2;

    //AMO identification for dcache
    assign lr = stage1.is_amo && (stage1.amo == AMO_LR);
    assign sc = stage1.is_amo && (stage1.amo == AMO_SC);
    assign is_amo = stage1.is_amo & ~(lr | sc);
    assign amo_op = stage1.amo;

    //Shared inputs
    assign d_inputs.addr = tlb.physical_address;
    assign d_inputs.load = stage1.load;
    assign d_inputs.store = stage1.store;
    assign d_inputs.be = be;
    assign d_inputs.fn3 = stage1.fn3;
    always_comb begin
        unique case(stage1.fn3) //<--011, 110, 111, 100, 101 unused
            LS_B_fn3 : d_inputs.data_in = {4{stage1_raw_data[7:0]}};
            LS_H_fn3 : d_inputs.data_in = {2{stage1_raw_data[15:0]}};
            LS_W_fn3 : d_inputs.data_in = stage1_raw_data;
        endcase
    end

    /*********************************
     *  Load attributes FIFO
     *********************************/
    lutram_fifo #(.DATA_WIDTH($bits(load_attributes_t)), .FIFO_DEPTH(ATTRIBUTES_DEPTH)) attributes_fifo (.fifo(load_attributes), .*);
    assign load_attributes.pop = load_complete;
    assign load_attributes.push = issue_request & stage1.load;
    assign load_attributes.data_in = load_attributes_in;
    assign stage2_attr  = load_attributes.data_out;

    assign load_attributes_in.unit_id = cache_access ? DCACHE_ID : (bus_access ? BUS_ID : BRAM_ID);
    assign load_attributes_in.fn3 = stage1.fn3;
    assign load_attributes_in.byte_addr = virtual_address[1:0];

    /*********************************
     *  Unit Instantiation
     *********************************/
    //BRAM
    generate if (USE_D_SCRATCH_MEM)
            dbram d_bram (.clk(clk), .rst(rst), .ls_inputs(d_inputs), .ls(ls_sub[BRAM_ID]), .data_out(unit_data_array[BRAM_ID]), .*);
        else
            assign  ls_sub[BRAM_ID].ready = 1;
    endgenerate
    generate
        if(FPGA_VENDOR == "xilinx") //AXI BUS
            axi_master axi_bus (.clk(clk), .rst(rst), .ls_inputs(d_inputs), .size({1'b0,stage1.fn3[1:0]}), .m_axi(m_axi),.ls(ls_sub[BUS_ID]), .data_out(unit_data_array[BUS_ID])); //Lower two bits of fn3 match AXI specification for request size (byte/halfword/word)
        else begin //Avalon bus
            avalon_master avalon_bus(.clk(clk), .rst(rst),
                    .addr(m_avalon.addr),
                    .avread(m_avalon.read),
                    .avwrite(m_avalon.write),
                    .byteenable(m_avalon.byteenable),
                    .readdata(m_avalon.readdata),
                    .writedata(m_avalon.writedata),
                    .waitrequest(m_avalon.waitrequest),
                    .readdatavalid(m_avalon.readdatavalid),
                    .writeresponsevalid(m_avalon.writeresponsevalid),
                    .addr_in(d_inputs.addr),
                    .data_in(d_inputs.data_in),
                    .data_out(unit_data_array[BUS_ID]),
                    .data_valid(ls_sub[BUS_ID].data_valid),
                    .ready(ls_sub[BUS_ID].ready),
                    .new_request(ls_sub[BUS_ID].new_request),
                    .rnw(d_inputs.load),
                    .be(d_inputs.be),
                    .data_ack(ls_sub[BUS_ID].ack)
                );
        end
    endgenerate

    //Cache
    generate if (USE_DCACHE)
            dcache data_cache (.clk(clk), .rst(rst), .ls_inputs(d_inputs), .ls(ls_sub[DCACHE_ID]), .is_amo(is_amo),  .use_forwarded_data( stage1.load_store_forward), .forwarded_data(most_recent_load), .data_out(unit_data_array[DCACHE_ID]), .*);
        else
            assign  ls_sub[DCACHE_ID].ready = 1;
    endgenerate
    /*************************************
     * Output Muxing
     *************************************/
    //unit mux
    assign unit_muxed_load_data = unit_data_array[stage2_attr.unit_id];

    //Byte select
    always_comb begin
        aligned_load_data[31:16] = unit_muxed_load_data[31:16];
        aligned_load_data[15:8] = (stage2_attr.byte_addr == 2'b00) ? unit_muxed_load_data[15:8] : unit_muxed_load_data[31:24];
        case(stage2_attr.byte_addr)
            2'b00 : aligned_load_data[7:0] = unit_muxed_load_data[7:0];
            2'b01 : aligned_load_data[7:0] = unit_muxed_load_data[15:8];
            2'b10 : aligned_load_data[7:0] = unit_muxed_load_data[23:16];
            2'b11 : aligned_load_data[7:0] = unit_muxed_load_data[31:24];
        endcase
    end

    //Sign extending
    always_comb begin
        unique case(stage2_attr.fn3)
            LS_B_fn3 : final_load_data = 32'(signed'(aligned_load_data[7:0]));
            LS_H_fn3 : final_load_data = 32'(signed'(aligned_load_data[15:0]));
            LS_W_fn3 : final_load_data = aligned_load_data;
                //unused 011
            L_BU_fn3 : final_load_data = 32'(unsigned'(aligned_load_data[7:0]));
            L_HU_fn3 : final_load_data = 32'(unsigned'(aligned_load_data[15:0]));
                //unused 110
                //unused 111
        endcase
    end

    always_ff @ (posedge clk) begin
        if (data_valid)
            previous_load <= final_load_data;
    end

    /*********************************
     *  Output FIFO
     *********************************/
    lutram_fifo #(.DATA_WIDTH(XLEN), .FIFO_DEPTH(LS_OUTPUT_BUFFER_DEPTH)) output_fifo (.fifo(wb_fifo), .*);

    assign wb_fifo.data_in = final_load_data;
    assign wb_fifo.push = load_complete;
    assign wb_fifo.pop = ls_wb.accepted;
    assign ls_wb.rd = wb_fifo.data_out;
    assign ls_wb.done = wb_fifo.valid;

    assign ls_wb.early_done = wb_fifo.early_valid;
    /*********************************************/


endmodule
