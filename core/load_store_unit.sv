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

module load_store_unit

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,
        input gc_outputs_t gc,

        input load_store_inputs_t ls_inputs,
        unit_issue_interface.unit issue,

        input logic dcache_on,
        input logic clear_reservation,
        tlb_interface.requester tlb,
        input logic tlb_on,

        l1_arbiter_request_interface.master l1_request,
        l1_arbiter_return_interface.master l1_response,
        input sc_complete,
        input sc_success,

        axi_interface.master m_axi,
        avalon_interface.master m_avalon,
        wishbone_interface.master dwishbone,

        local_memory_interface.master data_bram,

        //Writeback-Store Interface
        input wb_packet_t wb_snoop,

        //Retire release
        input id_t retire_ids [RETIRE_PORTS],
        input logic retire_port_valid [RETIRE_PORTS],

        exception_interface.unit exception,
        output load_store_status_t load_store_status,
        unit_writeback_interface.unit wb,

        output logic tr_load_conflict_delay
    );

    localparam NUM_SUB_UNITS = int'(CONFIG.INCLUDE_DLOCAL_MEM) + int'(CONFIG.INCLUDE_PERIPHERAL_BUS) + int'(CONFIG.INCLUDE_DCACHE);
    localparam NUM_SUB_UNITS_W = (NUM_SUB_UNITS == 1) ? 1 : $clog2(NUM_SUB_UNITS);

    localparam LOCAL_MEM_ID = 0;
    localparam BUS_ID = int'(CONFIG.INCLUDE_DLOCAL_MEM);
    localparam DCACHE_ID = int'(CONFIG.INCLUDE_DLOCAL_MEM) + int'(CONFIG.INCLUDE_PERIPHERAL_BUS);

    //Should be equal to pipeline depth of longest load/store subunit 
    localparam ATTRIBUTES_DEPTH = 2;//CONFIG.INCLUDE_DCACHE ? 2 : 1;

    //Subunit signals
    addr_utils_interface #(CONFIG.DLOCAL_MEM_ADDR.L, CONFIG.DLOCAL_MEM_ADDR.H) dlocal_mem_addr_utils ();
    addr_utils_interface #(CONFIG.PERIPHERAL_BUS_ADDR.L, CONFIG.PERIPHERAL_BUS_ADDR.H) dpbus_addr_utils ();
    addr_utils_interface #(CONFIG.DCACHE_ADDR.L, CONFIG.DCACHE_ADDR.H) dcache_addr_utils ();
    memory_sub_unit_interface sub_unit[NUM_SUB_UNITS-1:0]();

    addr_utils_interface #(CONFIG.DCACHE.NON_CACHEABLE.L, CONFIG.DCACHE.NON_CACHEABLE.H) uncacheable_utils ();

    logic [NUM_SUB_UNITS-1:0] sub_unit_address_match;

    data_access_shared_inputs_t shared_inputs;
    logic [31:0] unit_data_array [NUM_SUB_UNITS-1:0];
    logic [NUM_SUB_UNITS-1:0] unit_ready;
    logic [NUM_SUB_UNITS-1:0] unit_data_valid;
    logic [NUM_SUB_UNITS-1:0] last_unit;
    logic [NUM_SUB_UNITS-1:0] current_unit;

    logic units_ready;

    logic unit_switch;
    logic unit_switch_in_progress;
    logic unit_switch_hold;

    logic sub_unit_issue;
    logic load_complete;

    logic [31:0] virtual_address;

    logic [31:0] unit_muxed_load_data;
    logic [31:0] aligned_load_data;
    logic [31:0] final_load_data;


    logic unaligned_addr;
    logic load_exception_complete;
    logic fence_hold;

    typedef struct packed{
        logic is_halfword;
        logic is_signed;
        logic [1:0] byte_addr;
        logic [1:0] final_mux_sel;
        id_t id;
        logic [NUM_SUB_UNITS_W-1:0] subunit_id;
    } load_attributes_t;
    load_attributes_t  mem_attr, wb_attr;

    logic [3:0] be;
    //FIFOs
    fifo_interface #(.DATA_WIDTH($bits(load_attributes_t))) load_attributes();

    load_store_queue_interface lsq();
    logic tr_possible_load_conflict_delay;

    ////////////////////////////////////////////////////
    //Implementation
    ////////////////////////////////////////////////////


    ////////////////////////////////////////////////////
    //Alignment Exception
    generate if (CONFIG.INCLUDE_M_MODE) begin : gen_ls_exceptions
        logic new_exception;
        always_comb begin
            case(ls_inputs.fn3)
                LS_H_fn3, L_HU_fn3 : unaligned_addr = virtual_address[0];
                LS_W_fn3 : unaligned_addr = |virtual_address[1:0];
                default : unaligned_addr = 0;
            endcase
        end

        assign new_exception = unaligned_addr & issue.new_request & ~ls_inputs.fence;
        always_ff @(posedge clk) begin
            if (rst)
                exception.valid <= 0;
            else
                exception.valid <= (exception.valid & ~exception.ack) | new_exception;
        end

        always_ff @(posedge clk) begin
            if (new_exception & ~exception.valid) begin
                exception.code <= ls_inputs.store ? STORE_AMO_ADDR_MISSALIGNED : LOAD_ADDR_MISSALIGNED;
                exception.tval <= virtual_address;
                exception.id <= issue.id;
            end
        end

        always_ff @(posedge clk) begin
            if (rst)
                load_exception_complete <= 0;
            else
                load_exception_complete <= exception.valid & exception.ack & (exception.code == LOAD_ADDR_MISSALIGNED);
        end
    end endgenerate

    ////////////////////////////////////////////////////
    //Load-Store status
    assign load_store_status = '{
        sq_empty : lsq.sq_empty,
        no_released_stores_pending : lsq.no_released_stores_pending,
        idle : lsq.empty & (~load_attributes.valid) & units_ready
    };

    ////////////////////////////////////////////////////
    //TLB interface
    assign virtual_address = ls_inputs.rs1 + 32'(signed'(ls_inputs.offset));

    assign tlb.virtual_address = virtual_address;
    assign tlb.new_request = tlb_on & issue.new_request;
    assign tlb.execute = 0;
    assign tlb.rnw = ls_inputs.load & ~ls_inputs.store;

    ////////////////////////////////////////////////////
    //Byte enable generation
    //Only set on store
    //  SW: all bytes
    //  SH: upper or lower half of bytes
    //  SB: specific byte
    always_comb begin
        be = 0;
        case(ls_inputs.fn3[1:0])
            LS_B_fn3[1:0] : be[virtual_address[1:0]] = 1;
            LS_H_fn3[1:0] : begin
                be[virtual_address[1:0]] = 1;
                be[{virtual_address[1], 1'b1}] = 1;
            end
            default : be = '1;
        endcase
    end

    ////////////////////////////////////////////////////
    //Load Store Queue
    assign lsq.data_in = '{
        addr : tlb_on ? tlb.physical_address : virtual_address,
        fn3 : ls_inputs.fn3,
        be : be,
        data : ls_inputs.rs2,
        load : ls_inputs.load,
        store : ls_inputs.store,
        id : issue.id,
        forwarded_store : ls_inputs.forwarded_store,
        id_needed : ls_inputs.store_forward_id
    };

    assign lsq.potential_push = issue.possible_issue;
    assign lsq.push = issue.new_request & ~unaligned_addr & (~tlb_on | tlb.done) & ~ls_inputs.fence;

    load_store_queue  # (.CONFIG(CONFIG)) lsq_block (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .lsq (lsq),
        .wb_snoop (wb_snoop),
        .retire_ids (retire_ids),
        .retire_port_valid (retire_port_valid),
        .tr_possible_load_conflict_delay (tr_possible_load_conflict_delay)
    );
    assign shared_inputs = lsq.data_out;
    assign lsq.pop = sub_unit_issue;


    ////////////////////////////////////////////////////
    //Unit tracking
    assign current_unit = sub_unit_address_match;

    always_ff @ (posedge clk) begin
        if (load_attributes.push)
            last_unit <= sub_unit_address_match;
    end

    //When switching units, ensure no outstanding loads so that there can be no timing collisions with results
    assign unit_switch = (current_unit != last_unit) & load_attributes.valid;
    always_ff @ (posedge clk) begin
        unit_switch_in_progress <= (unit_switch_in_progress | unit_switch) & ~load_attributes.valid;
    end
    assign unit_switch_hold = unit_switch | unit_switch_in_progress;

    ////////////////////////////////////////////////////
    //Primary Control Signals
    assign units_ready = &unit_ready & (~unit_switch_hold);
    assign load_complete = |unit_data_valid;

    assign issue.ready = (~tlb_on | tlb.ready) & (~lsq.full) & (~fence_hold) & (~exception.valid);
    assign sub_unit_issue = lsq.valid & units_ready;

    always_ff @ (posedge clk) begin
        if (rst)
            fence_hold <= 0;
        else
            fence_hold <= (fence_hold & ~load_store_status.idle) | (issue.new_request & ls_inputs.fence);
    end

    ////////////////////////////////////////////////////
    //Load attributes FIFO
    logic [1:0] final_mux_sel;
    logic [NUM_SUB_UNITS_W-1:0] subunit_id;

    one_hot_to_integer #(NUM_SUB_UNITS)
    sub_unit_select (
        .one_hot (sub_unit_address_match), 
        .int_out (subunit_id)
    );

    always_comb begin
        case(shared_inputs.fn3)
            LS_B_fn3, L_BU_fn3 : final_mux_sel = 0;
            LS_H_fn3, L_HU_fn3 : final_mux_sel = 1;
            default : final_mux_sel = 2; //LS_W_fn3
        endcase
    end
    
    assign mem_attr = '{
        is_halfword : shared_inputs.fn3[0],
        is_signed : ~|shared_inputs.fn3[2:1],
        byte_addr : shared_inputs.addr[1:0],
        final_mux_sel : final_mux_sel,
        id : shared_inputs.id,
        subunit_id : subunit_id
    };

    assign load_attributes.data_in = mem_attr;
    assign load_attributes.push = sub_unit_issue & shared_inputs.load;
    assign load_attributes.potential_push = load_attributes.push;
    
    cva5_fifo #(.DATA_WIDTH($bits(load_attributes_t)), .FIFO_DEPTH(ATTRIBUTES_DEPTH))
    attributes_fifo (
        .clk (clk),
        .rst (rst), 
        .fifo (load_attributes)
    );

    assign load_attributes.pop = load_complete;
    assign wb_attr = load_attributes.data_out;
    ////////////////////////////////////////////////////
    //Unit Instantiation
    generate for (genvar i=0; i < NUM_SUB_UNITS; i++) begin : gen_load_store_sources
        assign sub_unit[i].new_request = sub_unit_issue & sub_unit_address_match[i];
        assign sub_unit[i].addr = shared_inputs.addr;
        assign sub_unit[i].re = shared_inputs.load;
        assign sub_unit[i].we = shared_inputs.store;
        assign sub_unit[i].be = shared_inputs.be;
        assign sub_unit[i].data_in = shared_inputs.data_in;

        assign unit_ready[i] = sub_unit[i].ready;
        assign unit_data_valid[i] = sub_unit[i].data_valid;
        assign unit_data_array[i] = sub_unit[i].data_out;
    end
    endgenerate

    generate if (CONFIG.INCLUDE_DLOCAL_MEM) begin : gen_ls_local_mem
        assign sub_unit_address_match[LOCAL_MEM_ID] = dlocal_mem_addr_utils.address_range_check(shared_inputs.addr);
        local_mem_sub_unit d_local_mem (
            .clk (clk), 
            .rst (rst),
            .unit (sub_unit[LOCAL_MEM_ID]),
            .local_mem (data_bram)
        );
        end
    endgenerate

    generate if (CONFIG.INCLUDE_PERIPHERAL_BUS) begin : gen_ls_pbus
            assign sub_unit_address_match[BUS_ID] = dpbus_addr_utils.address_range_check(shared_inputs.addr);
            if(CONFIG.PERIPHERAL_BUS_TYPE == AXI_BUS)
                axi_master axi_bus (
                    .clk (clk),
                    .rst (rst),
                    .m_axi (m_axi),
                    .size ({1'b0,shared_inputs.fn3[1:0]}),
                    .ls (sub_unit[BUS_ID])
                ); //Lower two bits of fn3 match AXI specification for request size (byte/halfword/word)
            else if (CONFIG.PERIPHERAL_BUS_TYPE == WISHBONE_BUS)
                wishbone_master wishbone_bus (
                    .clk (clk),
                    .rst (rst),
                    .wishbone (dwishbone),
                    .ls (sub_unit[BUS_ID])
                );
            else if (CONFIG.PERIPHERAL_BUS_TYPE == AVALON_BUS)  begin
                avalon_master avalon_bus (
                    .clk (clk),
                    .rst (rst),
                    .m_avalon (m_avalon), 
                    .ls (sub_unit[BUS_ID])
                );
            end
        end
    endgenerate

    generate if (CONFIG.INCLUDE_DCACHE) begin : gen_ls_dcache
            logic uncacheable;
            assign sub_unit_address_match[DCACHE_ID] = dcache_addr_utils.address_range_check(shared_inputs.addr);
            assign uncacheable = uncacheable_utils.address_range_check(shared_inputs.addr);

            dcache # (.CONFIG(CONFIG))
            data_cache (
                .clk (clk),
                .rst (rst),
                .dcache_on (dcache_on),
                .l1_request (l1_request),
                .l1_response (l1_response),
                .sc_complete (sc_complete),
                .sc_success (sc_success),
                .clear_reservation (clear_reservation),
                .amo (ls_inputs.amo),
                .uncacheable (uncacheable),
                .ls (sub_unit[DCACHE_ID])
            );
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Output Muxing
    logic sign_bit_data [4];
    logic [1:0] sign_bit_sel;
    logic sign_bit;
    
    assign unit_muxed_load_data = unit_data_array[wb_attr.subunit_id];

    //Byte/halfword select: assumes aligned operations
    assign aligned_load_data[31:16] = unit_muxed_load_data[31:16];
    assign aligned_load_data[15:8] = wb_attr.byte_addr[1] ? unit_muxed_load_data[31:24] : unit_muxed_load_data[15:8];
    assign aligned_load_data[7:0] = unit_muxed_load_data[wb_attr.byte_addr*8 +: 8];

    assign sign_bit_data = '{unit_muxed_load_data[7], unit_muxed_load_data[15], unit_muxed_load_data[23], unit_muxed_load_data[31]};
    assign sign_bit_sel = wb_attr.byte_addr | {1'b0, wb_attr.is_halfword};
    assign sign_bit = wb_attr.is_signed & sign_bit_data[sign_bit_sel];

    //Sign extending
    always_comb begin
        case(wb_attr.final_mux_sel)
            0 : final_load_data = {{24{sign_bit}}, aligned_load_data[7:0]};
            1 : final_load_data = {{16{sign_bit}}, aligned_load_data[15:0]};
            default : final_load_data = aligned_load_data; //LS_W_fn3
        endcase
    end

    ////////////////////////////////////////////////////
    //Output bank
    assign wb.rd = final_load_data;
    assign wb.done = load_complete | load_exception_complete;
    assign wb.id = load_exception_complete ? exception.id : wb_attr.id;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    spurious_load_complete_assertion:
        assert property (@(posedge clk) disable iff (rst) load_complete |-> (load_attributes.valid && unit_data_valid[wb_attr.subunit_id]))
        else $error("Spurious load complete detected!");

    // `ifdef ENABLE_SIMULATION_ASSERTIONS
    //     invalid_ls_address_assertion:
    //         assert property (@(posedge clk) disable iff (rst) (sub_unit_issue & ~ls_inputs.fence) |-> |sub_unit_address_match)
    //         else $error("invalid L/S address");
    // `endif

    ////////////////////////////////////////////////////
    //Trace Interface
    generate if (ENABLE_TRACE_INTERFACE) begin : gen_ls_trace
        assign tr_load_conflict_delay = tr_possible_load_conflict_delay & units_ready;
    end
    endgenerate

endmodule
