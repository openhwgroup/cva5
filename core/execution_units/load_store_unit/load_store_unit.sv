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
    import csr_types::*;
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

        mem_interface.rw_master mem,

        axi_interface.master m_axi,
        avalon_interface.master m_avalon,
        wishbone_interface.master dwishbone,

        local_memory_interface.master data_bram,

        //CSR
        input logic [1:0] current_privilege,
        input envcfg_t menvcfg,
        input envcfg_t senvcfg,

        //Writeback-Store Interface
        input wb_packet_t wb_packet [CONFIG.NUM_WB_GROUPS],
        input fp_wb_packet_t fp_wb_packet [2],

        //Retire
        input id_t retire_id,
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
    localparam ATTRIBUTES_DEPTH = 1;

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
    logic [NUM_SUB_UNITS_W-1:0] last_unit;

    logic sub_unit_ready;
    logic [NUM_SUB_UNITS_W-1:0] subunit_id;
    ls_subunit_t padded_subunit_id;

    logic unit_switch;
    logic unit_switch_in_progress;
    logic unit_switch_hold;

    logic sel_load;
    logic sub_unit_issue;
    logic sub_unit_load_issue;
    logic sub_unit_store_issue;

    logic load_response;
    logic load_complete;

    logic [31:0] virtual_address;

    logic [31:0] unit_muxed_load_data;
    logic [31:0] aligned_load_data;
    logic [31:0] final_load_data;

    logic tlb_request_r;
    logic tlb_lq;

    logic unaligned_addr;
    logic exception_is_fp;
    logic exception_is_store;
    logic nontrivial_fence;
    logic fence_hold;
    logic illegal_cbo;
    logic exception_lsq_push;
    logic nomatch_fault;
    logic late_exception;

    id_t exception_id;

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
        cbo_t cbo_type;
        logic is_fpu;
        logic is_double;
        logic nontrivial_fence;
        logic is_amo;
        amo_t amo_type;
        logic rd_zero;
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
        is_load : ~instruction.upper_opcode[5] & ~instruction.upper_opcode[3],
        is_store : instruction inside {SB, SH, SW} | CONFIG.INCLUDE_UNIT.FPU & instruction inside {SP_FSW, DP_FSD},
        is_fence : ~instruction.fn3[1] & instruction.upper_opcode[3],
        nontrivial_fence : nontrivial_fence,
        is_cbo : CONFIG.INCLUDE_CBO & instruction inside {CBO_INVAL, CBO_CLEAN, CBO_FLUSH},
        cbo_type : cbo_t'(instruction[21:20]),
        is_fpu : CONFIG.INCLUDE_UNIT.FPU & instruction.upper_opcode[3:2] == 2'b01,
        is_double : CONFIG.INCLUDE_UNIT.FPU & instruction.fn3[1:0] == 2'b11,
        is_amo : CONFIG.INCLUDE_AMO & instruction.upper_opcode[3] & instruction.upper_opcode[5],
        amo_type : amo_t'(instruction[31:27]),
        rd_zero : ~|instruction.rd_addr,
        offset : (CONFIG.INCLUDE_CBO | CONFIG.INCLUDE_AMO) & instruction[3] ? '0 : (instruction[5] ? store_offset : load_offset)
    };
    assign decode_is_store = decode_attr.is_store | decode_attr.is_cbo; //Must be exact

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
    //CSR Permissions
    //Can impact fences, atomic instructions, and CBO
    logic fiom; 
    logic fiom_amo_hold;
    generate if (CONFIG.MODES inside {MU, MSU}) begin : gen_csr_env
        //Fence on IO implies memory; force all fences to be nontrivial for simplicity
        always_comb begin
            if (CONFIG.MODES == MU)
                fiom = current_privilege == USER_PRIVILEGE & menvcfg.fiom;
            else
                fiom = (current_privilege != MACHINE_PRIVILEGE & menvcfg.fiom) | (current_privilege == USER_PRIVILEGE & senvcfg.fiom);
        end

        //AMO instructions AQ-RL consider all memory regions; force write drain for simplicity
        logic fiom_amo_hold_r;
        logic set_fiom_amo_hold;
        assign set_fiom_amo_hold = lsq.load_valid & shared_inputs.amo & fiom & write_outstanding;
        assign fiom_amo_hold = set_fiom_amo_hold | fiom_amo_hold_r;

        always_ff @(posedge clk) begin
            if (rst | ~write_outstanding)
                fiom_amo_hold_r <= 0;
            else
                fiom_amo_hold_r <= fiom_amo_hold_r | set_fiom_amo_hold;
        end
    end endgenerate

    ////////////////////////////////////////////////////
    //Exceptions
    generate if (CONFIG.MODES != BARE) begin : gen_ls_exceptions
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

        logic menv_illegal;
        logic senv_illegal;
        assign menv_illegal = CONFIG.INCLUDE_CBO & (issue_attr.is_cbo & issue_attr.cbo_type == INVAL ? menvcfg.cbie == 2'b00 : ~menvcfg.cbcfe);
        assign senv_illegal = CONFIG.INCLUDE_CBO & (issue_attr.is_cbo & issue_attr.cbo_type == INVAL ? senvcfg.cbie == 2'b00 : ~senvcfg.cbcfe);
        assign illegal_cbo = CONFIG.MODES == MU ? current_privilege == USER_PRIVILEGE & menv_illegal : (current_privilege != MACHINE_PRIVILEGE & menv_illegal) | (current_privilege == USER_PRIVILEGE & senv_illegal);

        assign nomatch_fault = tlb.done & ~|sub_unit_address_match;
        assign late_exception = tlb.is_fault | nomatch_fault;

        //Hold writeback exceptions until they are ready to retire
        logic rd_zero_r;
        logic delay_exception;
        logic delayed_exception;
        assign delay_exception = (
            (issue.new_request & unaligned_addr & (issue_attr.is_load | issue_attr.is_amo) & issue.id != retire_id & ~issue_attr.rd_zero) |
            (late_exception & tlb_lq & exception_id != retire_id & ~rd_zero_r)
        );
        always_ff @(posedge clk) begin
            if (rst)
                delayed_exception <= 0;
            else if (delay_exception)
                delayed_exception <= 1;
            else if (new_exception)
                delayed_exception <= 0;
        end

        assign new_exception = (
            (issue.new_request & ((unaligned_addr & issue_attr.is_store) | illegal_cbo)) |
            (issue.new_request & unaligned_addr & (issue_attr.is_load | issue_attr.is_amo) & (issue.id == retire_id | issue_attr.rd_zero)) |
            (late_exception & ~tlb_lq) |
            (late_exception & tlb_lq & (exception_id == retire_id | rd_zero_r)) |
            (delayed_exception & exception_id == retire_id)
        );

        always_ff @(posedge clk) begin
            if (rst)
                exception.valid <= 0;
            else
                exception.valid <= new_exception;
        end

        logic is_load;
        logic is_load_r;
        assign is_load = issue_attr.is_load & ~(issue_attr.is_amo & issue_attr.amo_type != AMO_LR_FN5);

        always_ff @(posedge clk) begin
            exception_lsq_push <= issue.new_request & ((unaligned_addr & ~issue_attr.is_fence & ~issue_attr.is_cbo) | illegal_cbo);
            if (issue.new_request) begin
                rd_zero_r <= issue_attr.rd_zero;
                exception_is_fp <= CONFIG.INCLUDE_UNIT.FPU & issue_attr.is_fpu;
                is_load_r <= is_load;
                if (illegal_cbo) begin
                    exception.code <= ILLEGAL_INST;
                    exception.tval <= issue_stage.instruction;
                end else begin
                    exception.code <= is_load ? LOAD_ADDR_MISSALIGNED : STORE_AMO_ADDR_MISSALIGNED;
                    exception.tval <= virtual_address;
                end
                exception_id <= issue.id;
            end
            else if (tlb.is_fault)
                exception.code <= is_load_r ? LOAD_PAGE_FAULT : STORE_OR_AMO_PAGE_FAULT;
            else if (nomatch_fault)
                exception.code <= is_load_r ? LOAD_FAULT : STORE_AMO_FAULT;
        end
        assign exception.possible = (tlb_request_r & (~tlb.done | ~|sub_unit_address_match)) | exception.valid | delayed_exception; //Must suppress issue for issue-time exceptions too
        assign exception.pc = issue_stage.pc_r;
        assign exception.discard = tlb_lq & ~rd_zero_r;

        assign exception_is_store = ~tlb_lq;
    end endgenerate

    ////////////////////////////////////////////////////
    //Load-Store status
    assign load_store_status = '{
        outstanding_store : ~lsq.sq_empty | write_outstanding,
        idle : lsq.empty & (~load_attributes.valid) & (&unit_ready) & (~write_outstanding)
    };

    ////////////////////////////////////////////////////
    //Address calculation
    assign virtual_address = rf[RS1] + 32'(signed'(issue_attr.offset));

    ////////////////////////////////////////////////////
    //TLB interface
    always_ff @(posedge clk) begin
        if (rst)
            tlb_request_r <= 0;
        else if (tlb.new_request)
            tlb_request_r <= 1;
        else if (tlb.done | tlb.is_fault)
            tlb_request_r <= 0;
    end

    assign tlb.rnw = issue_attr.is_load | (issue_attr.is_amo & issue_attr.amo_type == AMO_LR_FN5) | issue_attr.is_cbo;
    assign tlb.virtual_address = virtual_address;
    assign tlb.new_request = issue.new_request & ~issue_attr.is_fence & (~unaligned_addr | issue_attr.is_cbo) & ~illegal_cbo;

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
        offset : virtual_address[11:0],
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
    assign lsq.push = issue.new_request & ~issue_attr.is_fence;

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

    //Physical address passed separately
    assign lsq.addr_push = tlb.done | tlb.is_fault | exception_lsq_push;
    assign lsq.addr_data_in = '{
        addr : tlb.physical_address[31:12],
        rnw : tlb_lq,
        discard : late_exception | exception_lsq_push,
        subunit : padded_subunit_id
    };

    always_ff @(posedge clk) begin
        if (issue.new_request)
            tlb_lq <= ~issue_attr.is_store & ~issue_attr.is_cbo;
    end

    ////////////////////////////////////////////////////
    //Unit tracking
    always_ff @ (posedge clk) begin
        if (load_attributes.push)
            last_unit <= subunit_id;
    end

    //When switching units, ensure no outstanding loads so that there can be no timing collisions with results
    assign unit_switch = lsq.load_valid & (subunit_id != last_unit) & load_attributes.valid;
    always_ff @ (posedge clk) begin
        unit_switch_in_progress <= (unit_switch_in_progress | unit_switch) & ~load_attributes.valid;
    end
    assign unit_switch_hold = unit_switch | unit_switch_in_progress | fiom_amo_hold;

    ////////////////////////////////////////////////////
    //Primary Control Signals
    assign sel_load = lsq.load_valid;

    assign sub_unit_ready = unit_ready[subunit_id] & (~unit_switch_hold);
    assign load_response = |unit_data_valid;
    assign load_complete = load_response & (~exception.valid | exception_is_store);

    //TLB status and exceptions can be ignored because they will prevent instructions from issuing
    assign issue.ready = ~lsq.full & ~fence_hold;

    assign sub_unit_load_issue = sel_load & lsq.load_valid & sub_unit_ready;
    assign sub_unit_store_issue = (lsq.store_valid & ~sel_load) & sub_unit_ready;
    assign sub_unit_issue = sub_unit_load_issue | sub_unit_store_issue;

    assign write_outstanding = |unit_write_outstanding;

    always_ff @ (posedge clk) begin
        if (rst)
            fence_hold <= 0;
        else
            fence_hold <= (fence_hold & ~load_store_status.idle) | (issue.new_request & issue_attr.is_fence & (issue_attr.nontrivial_fence | fiom));
    end

    ////////////////////////////////////////////////////
    //Load attributes FIFO
    logic [1:0] final_mux_sel;

    assign subunit_id = shared_inputs.subunit[NUM_SUB_UNITS_W-1:0];
    one_hot_to_integer #(NUM_SUB_UNITS)
    sub_unit_select (
        .one_hot (sub_unit_address_match), 
        .int_out (padded_subunit_id[NUM_SUB_UNITS_W-1:0])
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
        assign sub_unit[i].new_request = sub_unit_issue & subunit_id == i;
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
        assign sub_unit_address_match[LOCAL_MEM_ID] = dlocal_mem_addr_utils.address_range_check(tlb.physical_address);
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
            assign sub_unit_address_match[BUS_ID] = dpbus_addr_utils.address_range_check(tlb.physical_address);
            if(CONFIG.PERIPHERAL_BUS_TYPE == AXI_BUS) begin : gen_axi
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
            end else if (CONFIG.PERIPHERAL_BUS_TYPE == WISHBONE_BUS) begin : gen_wishbone
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
            end else if (CONFIG.PERIPHERAL_BUS_TYPE == AVALON_BUS) begin : gen_avalon
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
            logic uncacheable_load;
            logic uncacheable_store;

            assign sub_unit_address_match[DCACHE_ID] = dcache_addr_utils.address_range_check(tlb.physical_address);

            assign uncacheable_load = CONFIG.DCACHE.USE_NON_CACHEABLE & uncacheable_utils.address_range_check(shared_inputs.addr);
            assign uncacheable_store = CONFIG.DCACHE.USE_NON_CACHEABLE & uncacheable_utils.address_range_check(shared_inputs.addr);

            if (CONFIG.DCACHE.USE_EXTERNAL_INVALIDATIONS) begin : gen_full_dcache
                dcache_inv #(.CONFIG(CONFIG)) data_cache (
                    .mem(mem),
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
            end else begin : gen_small_dcache
                dcache_noinv #(.CONFIG(CONFIG)) data_cache (
                    .mem(mem),
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
    assign wb.done = (load_complete & (~CONFIG.INCLUDE_UNIT.FPU | wb_attr.fp_op == INT_DONE)) | (exception.valid & ~exception_is_fp & ~exception_is_store);
    assign wb.id = exception.valid & ~exception_is_store ? exception_id : wb_attr.id;

    assign fp_wb.rd = fp_result;
    assign fp_wb.done = (load_complete & (wb_attr.fp_op == SINGLE_DONE | wb_attr.fp_op == DOUBLE_DONE)) | (exception.valid & exception_is_fp & ~exception_is_store);
    assign fp_wb.id = exception.valid & ~exception_is_store ? exception_id : wb_attr.id;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    spurious_load_complete_assertion:
        assert property (@(posedge clk) disable iff (rst) load_complete |-> (load_attributes.valid && unit_data_valid[wb_attr.subunit_id]))
        else $error("Spurious load complete detected!");


endmodule
