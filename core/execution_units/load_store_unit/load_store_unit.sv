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
    import fpu_types::*;
    import opcodes::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,
        input gc_outputs_t gc,

        input decode_packet_t decode_stage,
        output logic unit_needed,
        output logic [REGFILE_READ_PORTS-1:0] uses_rs,
        output logic [2:0] fp_uses_rs,
        output logic uses_rd,
        output logic fp_uses_rd,
        output logic decode_is_store,

        input issue_packet_t issue_stage,
        input logic issue_stage_ready,
        input logic instruction_issued_with_rd,
        input logic fp_instruction_issued_with_rd,
        input logic rs2_inuse,
        input logic fp_rs2_inuse,
        input rs_addr_t issue_rs_addr [REGFILE_READ_PORTS],
        input logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] issue_rd_wb_group,
        input logic fp_issue_rd_wb_group,
        input logic [31:0] rf [REGFILE_READ_PORTS],
        input logic[FLEN-1:0] fp_rf[3],

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
        input wb_packet_t wb_packet [CONFIG.NUM_WB_GROUPS],
        input fp_wb_packet_t fp_wb_packet [2],

        //Retire release
        input retire_packet_t store_retire,

        exception_interface.unit exception,
        output load_store_status_t load_store_status,
        unit_writeback_interface.unit wb,
        unit_writeback_interface.unit fp_wb
    );

    localparam NUM_SUB_UNITS = int'(CONFIG.INCLUDE_DLOCAL_MEM) + int'(CONFIG.INCLUDE_PERIPHERAL_BUS) + int'(CONFIG.INCLUDE_DCACHE);
    localparam NUM_SUB_UNITS_W = (NUM_SUB_UNITS == 1) ? 1 : $clog2(NUM_SUB_UNITS);

    localparam LOCAL_MEM_ID = 0;
    localparam BUS_ID = int'(CONFIG.INCLUDE_DLOCAL_MEM);
    localparam DCACHE_ID = int'(CONFIG.INCLUDE_DLOCAL_MEM) + int'(CONFIG.INCLUDE_PERIPHERAL_BUS);

    //Should be equal to pipeline depth of longest load/store subunit 
    localparam ATTRIBUTES_DEPTH = 2;

    //Subunit signals
    amo_interface amo_if[NUM_SUB_UNITS]();
    addr_utils_interface #(CONFIG.DLOCAL_MEM_ADDR.L, CONFIG.DLOCAL_MEM_ADDR.H) dlocal_mem_addr_utils ();
    addr_utils_interface #(CONFIG.PERIPHERAL_BUS_ADDR.L, CONFIG.PERIPHERAL_BUS_ADDR.H) dpbus_addr_utils ();
    addr_utils_interface #(CONFIG.DCACHE_ADDR.L, CONFIG.DCACHE_ADDR.H) dcache_addr_utils ();
    memory_sub_unit_interface sub_unit[NUM_SUB_UNITS-1:0]();

    addr_utils_interface #(CONFIG.DCACHE.NON_CACHEABLE.L, CONFIG.DCACHE.NON_CACHEABLE.H) uncacheable_utils ();

    logic [NUM_SUB_UNITS-1:0] sub_unit_address_match;

    data_access_shared_inputs_t shared_inputs;
    logic [31:0] unit_data_array [NUM_SUB_UNITS-1:0];
    logic [NUM_SUB_UNITS-1:0] unit_ready;
    logic [NUM_SUB_UNITS-1:0] unit_write_outstanding;
    logic write_outstanding;
    logic [NUM_SUB_UNITS-1:0] unit_data_valid;
    logic [NUM_SUB_UNITS-1:0] last_unit;

    logic sub_unit_ready;
    logic [NUM_SUB_UNITS_W-1:0] subunit_id;

    logic unit_switch;
    logic unit_switch_in_progress;
    logic unit_switch_hold;

    logic sel_load;
    logic sub_unit_issue;
    logic sub_unit_load_issue;
    logic sub_unit_store_issue;

    logic load_complete;

    logic [31:0] virtual_address;

    logic [31:0] unit_muxed_load_data;
    logic [31:0] aligned_load_data;
    logic [31:0] final_load_data;

    logic unaligned_addr;
    logic load_exception_complete;
    logic exception_is_fp;
    logic nontrivial_fence;
    logic fence_hold;

    typedef struct packed{
        logic is_signed;
        logic [1:0] byte_addr;
        logic [1:0] sign_sel;
        logic [1:0] final_mux_sel;
        id_t id;
        logic [NUM_SUB_UNITS_W-1:0] subunit_id;
        fp_ls_op_t fp_op;
    } load_attributes_t;
    load_attributes_t  wb_attr;

    common_instruction_t instruction;//rs1_addr, rs2_addr, fn3, fn7, rd_addr, upper/lower opcode

    logic [3:0] be;
    //FIFOs
    fifo_interface #(.DATA_TYPE(load_attributes_t)) load_attributes();

    load_store_queue_interface lsq();
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Decode
    assign instruction = decode_stage.instruction;

    assign unit_needed = instruction inside {LB, LH, LW, LBU, LHU, SB, SH, SW, FENCE} | 
        (CONFIG.INCLUDE_CBO & instruction inside {CBO_INVAL, CBO_CLEAN, CBO_FLUSH}) | 
        (CONFIG.INCLUDE_UNIT.FPU & instruction inside {SP_FLW, SP_FSW, DP_FLD, DP_FSD}) | 
        (CONFIG.INCLUDE_AMO & instruction inside {AMO_ADD, AMO_XOR, AMO_OR, AMO_AND, AMO_MIN, AMO_MAX, AMO_MINU, AMO_MAXU, AMO_SWAP, AMO_LR, AMO_SC});
    always_comb begin
        uses_rs = '0;
        uses_rs[RS1] = instruction inside {LB, LH, LW, LBU, LHU, SB, SH, SW} | 
            (CONFIG.INCLUDE_CBO & instruction inside {CBO_INVAL, CBO_CLEAN, CBO_FLUSH}) | 
            (CONFIG.INCLUDE_UNIT.FPU & instruction inside {SP_FLW, SP_FSW, DP_FLD, DP_FSD}) |
            (CONFIG.INCLUDE_AMO & instruction inside {AMO_ADD, AMO_XOR, AMO_OR, AMO_AND, AMO_MIN, AMO_MAX, AMO_MINU, AMO_MAXU, AMO_SWAP, AMO_LR, AMO_SC});
        if (CONFIG.INCLUDE_AMO)
            uses_rs[RS2] = instruction inside {AMO_ADD, AMO_XOR, AMO_OR, AMO_AND, AMO_MIN, AMO_MAX, AMO_MINU, AMO_MAXU, AMO_SWAP, AMO_SC};
        if (~CONFIG.INCLUDE_FORWARDING_TO_STORES)
            uses_rs[RS2] |= instruction inside {SB, SH, SW};
        uses_rd = instruction inside {LB, LH, LW, LBU, LHU} | (CONFIG.INCLUDE_AMO & instruction inside {AMO_ADD, AMO_XOR, AMO_OR, AMO_AND, AMO_MIN, AMO_MAX, AMO_MINU, AMO_MAXU, AMO_SWAP, AMO_LR, AMO_SC});
        fp_uses_rs = '0;
        fp_uses_rs[RS2] = ~CONFIG.INCLUDE_FORWARDING_TO_STORES & CONFIG.INCLUDE_UNIT.FPU & instruction inside {SP_FSW, DP_FSD};
        fp_uses_rd = CONFIG.INCLUDE_UNIT.FPU & instruction inside {SP_FLW, DP_FLD};
    end

    ////////////////////////////////////////////////////
    //LS specific decode support
    typedef struct packed{
        logic is_load;
        logic is_store;
        logic is_fence;
        logic is_cbo;
        logic is_fpu;
        logic is_double;
        logic nontrivial_fence;
        logic is_amo;
        amo_t amo_type;
        logic [11:0] offset;
    } ls_attr_t;
    ls_attr_t decode_attr;
    ls_attr_t issue_attr;

    logic [11:0] load_offset;
    logic [11:0] store_offset;
    assign load_offset = instruction[31:20];
    assign store_offset = {instruction[31:25], instruction[11:7]};

    //Only a reduced subset of possible fences require stalling, because of the following guarantees:
    //The load queue does not reorder loads
    //The store queue does not reorder stores
    //Earlier loads are always selected before later stores
    //The data cache and local memory are sequentially consistent (no reordering)
    //All peripheral busses are sequentially consistent across request types
    always_comb begin
        if (NUM_SUB_UNITS == 3)
            nontrivial_fence = (
                (instruction[27] & (instruction[22] | instruction[20])) | //Peripheral read before any write
                (instruction[26] & (instruction[23] | |instruction[21:20])) | //Peripheral write before anything other than a peripheral write
                (instruction[25] & instruction[22]) | //Regular read before peripheral write
                (instruction[24]) //Regular write before anything
            );
        else if (NUM_SUB_UNITS == 2 & ~CONFIG.INCLUDE_PERIPHERAL_BUS)
            nontrivial_fence = instruction[24] & |instruction[21:20]; //Regular write before any regular
        else if (NUM_SUB_UNITS == 2)
            nontrivial_fence = (
                (instruction[27] & (instruction[22] | instruction[20])) | //Peripheral read before any write
                (instruction[26] & (instruction[23] | |instruction[21:20])) | //Peripheral write before anything other than a peripheral write
                (instruction[25] & instruction[22]) | //Memory read before peripheral write
                (instruction[24] & |instruction[23:21]) //Memory write before anything other than a memory write
            );
        else if (NUM_SUB_UNITS == 1 & ~CONFIG.INCLUDE_PERIPHERAL_BUS)
            nontrivial_fence = instruction[24] & instruction[21]; //Memory write before memory read
        else if (NUM_SUB_UNITS == 1 & CONFIG.INCLUDE_PERIPHERAL_BUS)
            nontrivial_fence = (
                (instruction[27] & instruction[22]) | //Peripheral read before peripheral write
                (instruction[26] & instruction[23]) //Peripheral write before peripheral read
            );
        else //0 subunits??
            nontrivial_fence = 0;
    end

    assign decode_attr = '{
        is_load : instruction inside {LB, LH, LW, LBU, LHU} | CONFIG.INCLUDE_UNIT.FPU & instruction inside {SP_FLW, DP_FLD},
        is_store : instruction inside {SB, SH, SW} | CONFIG.INCLUDE_UNIT.FPU & instruction inside {SP_FSW, DP_FSD},
        is_fence : instruction inside {FENCE},
        nontrivial_fence : nontrivial_fence,
        is_cbo : CONFIG.INCLUDE_CBO & instruction inside {CBO_INVAL, CBO_CLEAN, CBO_FLUSH},
        is_fpu : CONFIG.INCLUDE_UNIT.FPU & instruction inside {SP_FLW, SP_FSW, DP_FLD, DP_FSD},
        is_double : CONFIG.INCLUDE_UNIT.FPU & instruction inside {DP_FLD, DP_FSD},
        is_amo : CONFIG.INCLUDE_AMO & instruction inside {AMO_ADD, AMO_XOR, AMO_OR, AMO_AND, AMO_MIN, AMO_MAX, AMO_MINU, AMO_MAXU, AMO_SWAP, AMO_LR, AMO_SC},
        amo_type : amo_t'(instruction[31:27]),
        offset : (CONFIG.INCLUDE_CBO | CONFIG.INCLUDE_AMO) & instruction[3] ? '0 : (instruction[5] ? store_offset : load_offset)
    };
    assign decode_is_store = decode_attr.is_store | decode_attr.is_cbo;

    always_ff @(posedge clk) begin
        if (issue_stage_ready)
            issue_attr <= decode_attr;
    end

    typedef struct packed{
        id_t id;
        logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] wb_group;
        logic fp_wb_group;
    } rd_attributes_t;
    rd_attributes_t rd_attributes;

    //Store FP instructions in 32-64
    lutram_1w_1r #(.DATA_TYPE(rd_attributes_t), .DEPTH(64))
    rd_to_id_table (
        .clk(clk),
        .waddr({fp_instruction_issued_with_rd, issue_stage.rd_addr}),
        .raddr({issue_attr.is_fpu, issue_rs_addr[RS2]}),
        .ram_write(instruction_issued_with_rd | fp_instruction_issued_with_rd),
        .new_ram_data('{
            id : issue_stage.id,
            wb_group : issue_rd_wb_group,
            fp_wb_group : fp_issue_rd_wb_group
        }),
        .ram_data_out(rd_attributes)
    );
    
    ////////////////////////////////////////////////////
    //Alignment Exception
    generate if (CONFIG.INCLUDE_M_MODE) begin : gen_ls_exceptions
        logic new_exception;
        always_comb begin
            if (issue_stage.fn3 == LS_H_fn3 | issue_stage.fn3 == L_HU_fn3)
                unaligned_addr = virtual_address[0];
            else if (issue_stage.fn3 == LS_W_fn3)
                unaligned_addr = |virtual_address[1:0];
            //Double-precision operations raise if not aligned on 8 byte boundary even though they are decomposed into 4 byte operations
            //This is because the operation might straddle two memory regions
            else if (CONFIG.INCLUDE_UNIT.FPU & issue_stage.fn3 == LS_D_fn3)
                unaligned_addr = |virtual_address[2:0];
            else
                unaligned_addr = 0;
        end

        assign new_exception = unaligned_addr & issue.new_request & ~issue_attr.is_fence & ~issue_attr.is_cbo;
        always_ff @(posedge clk) begin
            if (rst)
                exception.valid <= 0;
            else
                exception.valid <= (exception.valid & ~exception.ack) | new_exception;
        end

        always_ff @(posedge clk) begin
            if (rst)
                exception_is_fp <= 0;
            else if (new_exception)
                exception_is_fp <= CONFIG.INCLUDE_UNIT.FPU & issue_attr.is_fpu;
        end

        always_ff @(posedge clk) begin
            if (new_exception & ~exception.valid) begin
                exception.code <= issue_attr.is_store ? STORE_AMO_ADDR_MISSALIGNED : LOAD_ADDR_MISSALIGNED;
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
        idle : lsq.empty & (~load_attributes.valid) & (&unit_ready) & (~write_outstanding)
    };

    ////////////////////////////////////////////////////
    //TLB interface
    assign virtual_address = rf[RS1] + 32'(signed'(issue_attr.offset));

    assign tlb.virtual_address = virtual_address;
    assign tlb.new_request = tlb_on & issue.new_request & ~issue_attr.is_fence;
    assign tlb.execute = 0;
    assign tlb.rnw = issue_attr.is_load & ~issue_attr.is_store;

    ////////////////////////////////////////////////////
    //Byte enable generation
    //Only set on store
    //  SW: all bytes
    //  SH: upper or lower half of bytes
    //  SB: specific byte
    always_comb begin
        be = 0;
        case(issue_stage.fn3[1:0])
            LS_B_fn3[1:0] : be[virtual_address[1:0]] = 1;
            LS_H_fn3[1:0] : begin
                be[virtual_address[1:0]] = 1;
                be[{virtual_address[1], 1'b1}] = 1;
            end
            default : be = '1;
        endcase
        if (issue_attr.is_cbo) //Treat CBOM as writes that don't do anything
            be = '0;
    end

    ////////////////////////////////////////////////////
    //Load Store Queue
    assign lsq.data_in = '{
        addr : tlb_on ? tlb.physical_address : virtual_address,
        fn3 : issue_stage.fn3,
        be : be,
        data : rf[RS2],
        load : issue_attr.is_load | issue_attr.is_amo,
        store : issue_attr.is_store,
        cache_op : issue_attr.is_cbo,
        amo : issue_attr.is_amo,
        amo_type : issue_attr.amo_type,
        id : issue.id,
        id_needed : rd_attributes.id,
        fp : issue_attr.is_fpu,
        double : issue_attr.is_double,
        fp_data : fp_rf[RS2]
    };

    assign lsq.potential_push = issue.possible_issue;
    assign lsq.push = issue.new_request & (~unaligned_addr | issue_attr.is_cbo) & (~tlb_on | tlb.done) & ~issue_attr.is_fence;

    load_store_queue  # (.CONFIG(CONFIG)) lsq_block (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .lsq (lsq),
        .store_forward_wb_group (rs2_inuse ? rd_attributes.wb_group : '0),
        .fp_store_forward_wb_group ({fp_rs2_inuse & rd_attributes.fp_wb_group, fp_rs2_inuse & ~rd_attributes.fp_wb_group}),
        .wb_packet (wb_packet),
        .fp_wb_packet (fp_wb_packet),
        .store_retire (store_retire)
    );
    assign shared_inputs = sel_load ? lsq.load_data_out : lsq.store_data_out;
    assign lsq.load_pop = sub_unit_load_issue;
    assign lsq.store_pop = sub_unit_store_issue;

    ////////////////////////////////////////////////////
    //Unit tracking
    always_ff @ (posedge clk) begin
        if (load_attributes.push)
            last_unit <= sub_unit_address_match;
    end

    //When switching units, ensure no outstanding loads so that there can be no timing collisions with results
    assign unit_switch = lsq.load_valid & (sub_unit_address_match != last_unit) & load_attributes.valid;
    always_ff @ (posedge clk) begin
        unit_switch_in_progress <= (unit_switch_in_progress | unit_switch) & ~load_attributes.valid;
    end
    assign unit_switch_hold = unit_switch | unit_switch_in_progress;

    ////////////////////////////////////////////////////
    //Primary Control Signals
    assign sel_load = lsq.load_valid;

    assign sub_unit_ready = unit_ready[subunit_id] & (~unit_switch_hold);
    assign load_complete = |unit_data_valid;

    assign issue.ready = (~tlb_on | tlb.ready) & (~lsq.full) & (~fence_hold) & (~exception.valid);

    assign sub_unit_load_issue = sel_load & lsq.load_valid & sub_unit_ready & sub_unit_address_match[subunit_id];
    assign sub_unit_store_issue = (lsq.store_valid & ~sel_load) & sub_unit_ready & sub_unit_address_match[subunit_id];
    assign sub_unit_issue = sub_unit_load_issue | sub_unit_store_issue;

    assign write_outstanding = |unit_write_outstanding;

    always_ff @ (posedge clk) begin
        if (rst)
            fence_hold <= 0;
        else
            fence_hold <= (fence_hold & ~load_store_status.idle) | (issue.new_request & issue_attr.is_fence & issue_attr.nontrivial_fence);
    end

    ////////////////////////////////////////////////////
    //Load attributes FIFO
    logic [1:0] final_mux_sel;

    one_hot_to_integer #(NUM_SUB_UNITS)
    sub_unit_select (
        .one_hot (sub_unit_address_match), 
        .int_out (subunit_id)
    );

    always_comb begin
        case(lsq.load_data_out.fn3)
            LS_B_fn3, L_BU_fn3 : final_mux_sel = 0;
            LS_H_fn3, L_HU_fn3 : final_mux_sel = 1;
            default : final_mux_sel = 2; //LS_W_fn3
        endcase
    end
    
    assign load_attributes.data_in = '{
        is_signed : ~|lsq.load_data_out.fn3[2:1],
        byte_addr : lsq.load_data_out.addr[1:0],
        sign_sel : lsq.load_data_out.addr[1:0] | {1'b0, lsq.load_data_out.fn3[0]},//halfword
        final_mux_sel : final_mux_sel,
        id : lsq.load_data_out.id,
        subunit_id : subunit_id,
        fp_op : lsq.load_data_out.fp_op
    };
    assign load_attributes.push = sub_unit_load_issue;
    assign load_attributes.potential_push = load_attributes.push;
    
    cva5_fifo #(.DATA_TYPE(load_attributes_t), .FIFO_DEPTH(ATTRIBUTES_DEPTH))
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
            .write_outstanding (unit_write_outstanding[LOCAL_MEM_ID]),
            .amo (shared_inputs.amo),
            .amo_type (shared_inputs.amo_type),
            .amo_unit (amo_if[LOCAL_MEM_ID]),
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
                    .write_outstanding (unit_write_outstanding[BUS_ID]),
                    .m_axi (m_axi),
                    .amo (shared_inputs.amo),
                    .amo_type (shared_inputs.amo_type),
                    .amo_unit (amo_if[BUS_ID]),
                    .ls (sub_unit[BUS_ID])
                ); //Lower two bits of fn3 match AXI specification for request size (byte/halfword/word)
            else if (CONFIG.PERIPHERAL_BUS_TYPE == WISHBONE_BUS)
                wishbone_master #(.LR_WAIT(CONFIG.AMO_UNIT.LR_WAIT), .INCLUDE_AMO(CONFIG.INCLUDE_AMO)) wishbone_bus (
                    .clk (clk),
                    .rst (rst),
                    .write_outstanding (unit_write_outstanding[BUS_ID]),
                    .wishbone (dwishbone),
                    .amo (shared_inputs.amo),
                    .amo_type (shared_inputs.amo_type),
                    .amo_unit (amo_if[BUS_ID]),
                    .ls (sub_unit[BUS_ID])
                );
            else if (CONFIG.PERIPHERAL_BUS_TYPE == AVALON_BUS)  begin
                avalon_master #(.LR_WAIT(CONFIG.AMO_UNIT.LR_WAIT), .INCLUDE_AMO(CONFIG.INCLUDE_AMO)) avalon_bus (
                    .clk (clk),
                    .rst (rst),
                    .write_outstanding (unit_write_outstanding[BUS_ID]),
                    .m_avalon (m_avalon),
                    .amo (shared_inputs.amo),
                    .amo_type (shared_inputs.amo_type),
                    .amo_unit (amo_if[BUS_ID]),
                    .ls (sub_unit[BUS_ID])
                );
            end
        end
    endgenerate

    generate if (CONFIG.INCLUDE_DCACHE) begin : gen_ls_dcache
            logic load_ready;
            logic store_ready;
            logic uncacheable_load;
            logic uncacheable_store;
            logic dcache_load_request;
            logic dcache_store_request;

            assign sub_unit_address_match[DCACHE_ID] = dcache_addr_utils.address_range_check(shared_inputs.addr);

            assign uncacheable_load = CONFIG.DCACHE.USE_NON_CACHEABLE & uncacheable_utils.address_range_check(shared_inputs.addr);
            assign uncacheable_store = CONFIG.DCACHE.USE_NON_CACHEABLE & uncacheable_utils.address_range_check(shared_inputs.addr);

            assign dcache_load_request = sub_unit_load_issue & sub_unit_address_match[DCACHE_ID];
            assign dcache_store_request = sub_unit_store_issue & sub_unit_address_match[DCACHE_ID];

            dcache_litex #(.CONFIG(CONFIG)) data_cache (
                .l1_request(l1_request),
                .l1_response(l1_response),
                .write_outstanding(unit_write_outstanding[DCACHE_ID]),
                .amo(shared_inputs.amo),
                .amo_type(shared_inputs.amo_type),
                .amo_unit(amo_if[DCACHE_ID]),
                .uncacheable(uncacheable_load | uncacheable_store),
                .cbo(shared_inputs.cache_op),
                .ls(sub_unit[DCACHE_ID]),
                .load_peek(lsq.load_valid),
                .load_addr_peek(lsq.load_data_out.addr),
            .*);
        end
    endgenerate

    generate if (CONFIG.INCLUDE_AMO) begin : gen_amo
        amo_unit #(
            .NUM_UNITS(NUM_SUB_UNITS),
            .RESERVATION_WORDS(CONFIG.AMO_UNIT.RESERVATION_WORDS)
        ) amo_inst (
            .agents(amo_if),
        .*);
    end endgenerate

    ////////////////////////////////////////////////////
    //Output Muxing
    logic sign_bit_data [4];
    logic sign_bit;
    
    assign unit_muxed_load_data = unit_data_array[wb_attr.subunit_id];

    //Byte/halfword select: assumes aligned operations
    assign aligned_load_data[31:16] = unit_muxed_load_data[31:16];
    assign aligned_load_data[15:8] = wb_attr.byte_addr[1] ? unit_muxed_load_data[31:24] : unit_muxed_load_data[15:8];
    assign aligned_load_data[7:0] = unit_muxed_load_data[wb_attr.byte_addr*8 +: 8];

    assign sign_bit_data = '{unit_muxed_load_data[7], unit_muxed_load_data[15], unit_muxed_load_data[23], unit_muxed_load_data[31]};
    assign sign_bit = wb_attr.is_signed & sign_bit_data[wb_attr.sign_sel];

    //Sign extending
    always_comb begin
        case(wb_attr.final_mux_sel)
            0 : final_load_data = {{24{sign_bit}}, aligned_load_data[7:0]};
            1 : final_load_data = {{16{sign_bit}}, aligned_load_data[15:0]};
            default : final_load_data = aligned_load_data; //LS_W_fn3
        endcase
    end

    //FP buffering first load result
    logic[FLEN-1:0] fp_result;
    generate if (CONFIG.INCLUDE_UNIT.FPU && FLEN > 32) begin : gen_fp_load_buffering
        logic[31:0] saved_msb;
        always_ff @(posedge clk) begin
            if (rst)
                saved_msb <= '1;
            else begin
                if (load_complete & wb_attr.fp_op == DOUBLE_HOLD)
                    saved_msb <= unit_muxed_load_data;
                else if (load_complete) //Boxing
                    saved_msb <= '1;
            end
        end
        always_comb begin
            fp_result = '1;
            fp_result[FLEN-1-:32] = saved_msb;
            if (wb_attr.fp_op == SINGLE_DONE)
                fp_result[FLEN_F-1:0] = unit_muxed_load_data[31-:FLEN_F];
            else
                fp_result[FLEN-33:0] = unit_muxed_load_data[31-:FLEN-32];
        end
    end else if (CONFIG.INCLUDE_UNIT.FPU) begin : gen_fpu_no_buffering
        //No buffering ever required - all results are final
        assign fp_result = wb_attr.fp_op == SINGLE_DONE ? {{(FLEN-FLEN_F){1'b1}}, unit_muxed_load_data[31-:FLEN_F]} : unit_muxed_load_data[31-:FLEN];
    end
    else begin : gen_no_fpu
        assign fp_result = 'x;
    end endgenerate

    ////////////////////////////////////////////////////
    //Output bank
    assign wb.rd = final_load_data;
    assign wb.done = (load_complete & (~CONFIG.INCLUDE_UNIT.FPU | wb_attr.fp_op == INT_DONE)) | (load_exception_complete & ~exception_is_fp);
    //TODO: exceptions seemingly clobber load data if it appears on the same cycle
    assign wb.id = load_exception_complete ? exception.id : wb_attr.id;

    assign fp_wb.rd = fp_result;
    assign fp_wb.done = (load_complete & (wb_attr.fp_op == SINGLE_DONE | wb_attr.fp_op == DOUBLE_DONE)) | (load_exception_complete & exception_is_fp);
    assign fp_wb.id = load_exception_complete ? exception.id : wb_attr.id;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    spurious_load_complete_assertion:
        assert property (@(posedge clk) disable iff (rst) load_complete |-> (load_attributes.valid && unit_data_valid[wb_attr.subunit_id]))
        else $error("Spurious load complete detected!");


endmodule
