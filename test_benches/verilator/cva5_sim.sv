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

module cva5_sim 

    import cva5_config::*;
    import l2_config_and_types::*;
    import riscv_types::*;
    import cva5_types::*;

    # (
        parameter MEMORY_FILE = "/home/ematthew/Research/RISCV/software/riscv-tools/riscv-tests/benchmarks/dhrystone.riscv.hw_init" //change this to appropriate location "/home/ematthew/Downloads/dhrystone.riscv.sim_init"
    )
    (
        input logic clk,
        input logic rst,

        //DDR AXI
        output logic [31:0]ddr_axi_araddr,
        output logic [1:0]ddr_axi_arburst,
        output logic [3:0]ddr_axi_arcache,
        output logic [5:0]ddr_axi_arid,
        output logic [7:0]ddr_axi_arlen,
        output logic [0:0]ddr_axi_arlock,
        output logic [2:0]ddr_axi_arprot,
        output logic [3:0]ddr_axi_arqos,
        input logic ddr_axi_arready,
        output logic [3:0]ddr_axi_arregion,
        output logic [2:0]ddr_axi_arsize,
        output logic ddr_axi_arvalid,
        output logic [31:0]ddr_axi_awaddr,
        output logic [1:0]ddr_axi_awburst,
        output logic [3:0]ddr_axi_awcache,
        output logic [5:0]ddr_axi_awid,
        output logic [7:0]ddr_axi_awlen,
        output logic [0:0]ddr_axi_awlock,
        output logic [2:0]ddr_axi_awprot,
        output logic [3:0]ddr_axi_awqos,
        input logic ddr_axi_awready,
        output logic [3:0]ddr_axi_awregion,
        output logic [2:0]ddr_axi_awsize,
        output logic ddr_axi_awvalid,
        output logic [5:0]ddr_axi_bid,
        output logic ddr_axi_bready,
        input logic [1:0]ddr_axi_bresp,
        input logic ddr_axi_bvalid,
        input logic [31:0]ddr_axi_rdata,
        input logic [5:0]ddr_axi_rid,
        input logic ddr_axi_rlast,
        output logic ddr_axi_rready,
        input logic [1:0]ddr_axi_rresp,
        input logic ddr_axi_rvalid,
        output logic [31:0]ddr_axi_wdata,
        output logic ddr_axi_wlast,
        input logic ddr_axi_wready,
        output logic [3:0]ddr_axi_wstrb,
        output logic ddr_axi_wvalid,
        output logic [5:0]ddr_axi_wid,

        //L2 interface
        input logic [29:0] addr,
        input logic [3:0] be,
        input logic rnw,
        input logic is_amo,
        input logic [4:0] amo_type_or_burst_size,
        input logic [L2_SUB_ID_W-1:0] sub_id,

        input logic request_push,
        output logic request_full,

        output logic [31:2] inv_addr,
        output logic inv_valid,
        input logic inv_ack,

        output logic con_result,
        output logic con_valid,

        input logic [31:0] wr_data,
        input logic wr_data_push,
        output logic data_full,

        output logic [31:0] rd_data,
        output logic [L2_SUB_ID_W-1:0] rd_sub_id,
        output logic rd_data_valid,
        input logic rd_data_ack,

        //        //AXI bus
        //        output logic [31:0]bus_axi_araddr,
        //        output logic [1:0]bus_axi_arburst,
        //        output logic [3:0]bus_axi_arcache,
        //        output logic [5:0]bus_axi_arid,
        //        output logic [7:0]bus_axi_arlen,
        //        output logic [0:0]bus_axi_arlock,
        //        output logic [2:0]bus_axi_arprot,
        //        output logic [3:0]bus_axi_arqos,
        //        input logic bus_axi_arready,
        //        output logic [3:0]bus_axi_arregion,
        //        output logic [2:0]bus_axi_arsize,
        //        output logic bus_axi_arvalid,
        //        output logic [31:0]bus_axi_awaddr,
        //        output logic [1:0]bus_axi_awburst,
        //        output logic [3:0]bus_axi_awcache,
        //        output logic [5:0]bus_axi_awid,
        //        output logic [7:0]bus_axi_awlen,
        //        output logic [0:0]bus_axi_awlock,
        //        output logic [2:0]bus_axi_awprot,
        //        output logic [3:0]bus_axi_awqos,
        //        input logic bus_axi_awready,
        //        output logic [3:0]bus_axi_awregion,
        //        output logic [2:0]bus_axi_awsize,
        //        output logic bus_axi_awvalid,
        //        output logic [5:0]bus_axi_bid,
        //        output logic bus_axi_bready,
        //        input logic [1:0]bus_axi_bresp,
        //        input logic bus_axi_bvalid,
        //        input logic [31:0]bus_axi_rdata,
        //        output logic [5:0]bus_axi_rid,
        //        output logic bus_axi_rlast,
        //        output logic bus_axi_rready,
        //        input logic [1:0]bus_axi_rresp,
        //        input logic bus_axi_rvalid,
        //        output logic [31:0]bus_axi_wdata,
        //        output logic bus_axi_wlast,
        //        input logic bus_axi_wready,
        //        output logic [3:0]bus_axi_wstrb,
        //        output logic bus_axi_wvalid,
        //        output logic [5:0]bus_axi_wid,

        //Local Memory
        output logic [29:0] instruction_bram_addr,
        output logic instruction_bram_en,
        output logic [3:0] instruction_bram_be,
        output logic [31:0] instruction_bram_data_in,
        input logic [31:0] instruction_bram_data_out,

        output logic [29:0] data_bram_addr,
        output logic data_bram_en,
        output logic [3:0] data_bram_be,
        output logic [31:0] data_bram_data_in,
        input logic [31:0] data_bram_data_out,

        //Used by verilator
        output logic write_uart,
        output logic [7:0] uart_byte,

        //Trace Interface
        output integer NUM_RETIRE_PORTS,
        output logic [31:0] retire_ports_instruction [RETIRE_PORTS],
        output logic [31:0] retire_ports_pc [RETIRE_PORTS],
        output logic retire_ports_valid [RETIRE_PORTS],
        output logic store_queue_empty
    );

    logic [3:0] WRITE_COUNTER_MAX;
    logic [3:0] READ_COUNTER_MAX;
    assign READ_COUNTER_MAX = 4'b0101;
    assign WRITE_COUNTER_MAX = 4'b0101;

    //AXI memory
    logic [31:0]axi_araddr;
    logic [1:0]axi_arburst;
    logic [3:0]axi_arcache;
    logic [5:0]axi_arid;
    logic [7:0]axi_arlen;
    logic [0:0]axi_arlock;
    logic [2:0]axi_arprot;
    logic [3:0]axi_arqos;
    logic axi_arready;
    logic [3:0]axi_arregion;
    logic [2:0]axi_arsize;
    logic axi_arvalid;
    logic [31:0]axi_awaddr;
    logic [1:0]axi_awburst;
    logic [3:0]axi_awcache;
    logic [5:0]axi_awid;
    logic [7:0]axi_awlen;
    logic [0:0]axi_awlock;
    logic [2:0]axi_awprot;
    logic [3:0]axi_awqos;
    logic axi_awready;
    logic [3:0]axi_awregion;
    logic [2:0]axi_awsize;
    logic axi_awvalid;
    logic [5:0]axi_bid;
    logic axi_bready;
    logic [1:0]axi_bresp;
    logic axi_bvalid;
    logic [31:0]axi_rdata;
    logic [5:0]axi_rid;
    logic axi_rlast;
    logic axi_rready;
    logic [1:0]axi_rresp;
    logic axi_rvalid;
    logic [31:0]axi_wdata;
    logic axi_wlast;
    logic axi_wready;
    logic [3:0]axi_wstrb;
    logic axi_wvalid;
    logic [5:0]axi_wid;

    parameter SCRATCH_MEM_KB = 128;
    parameter MEM_LINES = (SCRATCH_MEM_KB*1024)/4;

    interrupt_t s_interrupt;
    interrupt_t m_interrupt;

    assign s_interrupt = '{default: 0};
    assign m_interrupt = '{default: 0};

    axi_interface m_axi();
    //axi_interface ddr_axi();
    avalon_interface m_avalon();
    wishbone_interface dwishbone();
    wishbone_interface iwishbone();

    l2_requester_interface l2[L2_NUM_PORTS-1:0]();
    l2_memory_interface mem();

    local_memory_interface instruction_bram();
    local_memory_interface data_bram();

    //    assign m_axi.arready = bus_axi_arready;
    //    assign bus_axi_arvalid = m_axi.arvalid;
    //    assign bus_axi_araddr = m_axi.araddr;
    //
    //
    //    //read data
    //    assign bus_axi_rready = m_axi.rready;
    //    assign m_axi.rvalid = bus_axi_rvalid;
    //    assign m_axi.rdata = bus_axi_rdata;
    //    assign m_axi.rresp = bus_axi_rresp;
    //
    //    //Write channel
    //    //write address
    //    assign m_axi.awready = bus_axi_awready;
    //    assign bus_axi_awaddr = m_axi.awaddr;
    //    assign bus_axi_awvalid = m_axi.awvalid;
    //
    //
    //    //write data
    //    assign m_axi.wready = bus_axi_wready;
    //    assign bus_axi_wvalid = m_axi. wvalid;
    //    assign bus_axi_wdata = m_axi.wdata;
    //    assign bus_axi_wstrb = m_axi.wstrb;
    //
    //    //write response
    //    assign bus_axi_bready = m_axi.bready;
    //    assign m_axi.bvalid = bus_axi_bvalid;
    //    assign m_axi.bresp = bus_axi_bresp;

    assign l2[1].request_push = 0;
    assign l2[1].wr_data_push = 0;
    assign l2[1].inv_ack = l2[1].inv_valid;
    assign l2[1].rd_data_ack = l2[1].rd_data_valid;

    axi_to_arb l2_to_mem (.*, .l2(mem));
    l2_arbiter l2_arb (.*, .request(l2));

    assign instruction_bram_addr = instruction_bram.addr;
    assign instruction_bram_en = instruction_bram.en;
    assign instruction_bram_be = instruction_bram.be;
    assign instruction_bram_data_in = instruction_bram.data_in;
    assign instruction_bram.data_out = instruction_bram_data_out;

    assign data_bram_addr = data_bram.addr;
    assign data_bram_en = data_bram.en;
    assign data_bram_be = data_bram.be;
    assign data_bram_data_in = data_bram.data_in;
    assign data_bram.data_out = data_bram_data_out;

    cva5 #(.CONFIG(EXAMPLE_CONFIG)) cpu(.*, .l2(l2[0]));

    //read channel
    logic[3:0] read_counter;
    logic begin_read_counter;

    always_ff @(posedge clk) begin
        if (rst) begin
            m_axi.rvalid <= 0;
            m_axi.arready <= 1; //You want it to start at ready
            m_axi.rresp <= 0;
            read_counter <= READ_COUNTER_MAX;
        end
        else begin
            if(m_axi.arready == 1 && m_axi.arvalid == 1) begin
                m_axi.arready <= 0;
                begin_read_counter <= 1;
                m_axi.rdata <= 32'hFFFFFF21;
            end

            if(begin_read_counter) begin
                if(read_counter == 0) begin
                    m_axi.rvalid <= 1;
                    m_axi.arready <= 1;
                    read_counter <= READ_COUNTER_MAX;
                    begin_read_counter <= 0;
                end
                else begin
                    read_counter <= read_counter - 1;
                    m_axi.rvalid <= 0;
                end
            end

            if(m_axi.rvalid &&  m_axi.rready) begin
                m_axi.rvalid <= 0;
            end

        end
    end

    //Write channel
    //write address
    logic[3:0] write_counter;
    logic begin_write_counter;

    always_ff @(posedge clk) begin
        if (rst) begin
            m_axi.wready <= 0;
            m_axi.awready <= 1; //You want it to start at ready
            m_axi.bresp <= 0;
            write_counter <= WRITE_COUNTER_MAX;
        end
        else begin
            if(m_axi.awready == 1 && m_axi.awvalid == 1) begin
                m_axi.awready <= 0;
                begin_write_counter <= 1;
            end

            if(begin_write_counter) begin
                if(write_counter == 0) begin
                    m_axi.awready <= 1;
                    m_axi.wready <= 1;
                    write_counter <= WRITE_COUNTER_MAX;
                    begin_write_counter <= 0;
                end
                else begin
                    write_counter <= write_counter - 1;
                    m_axi.wready <= 0;
                end
            end

            if(m_axi.bready == 1 && m_axi.wready) begin
                m_axi.bvalid <= 1;
                m_axi.bresp <= 0;
            end
            else begin
                m_axi.bvalid <= 0;
                m_axi.bresp <= 0;
            end

            if(m_axi.wready & m_axi.wvalid) begin
                m_axi.wready <= 0;
            end
        end
    end

    initial begin
        write_uart = 0;
        uart_byte = 0;
    end
    //Capture writes to UART
    always_ff @(posedge clk) begin
        write_uart <= (m_axi.wvalid && m_axi.wready && m_axi.awaddr[13:0] == 4096);
        uart_byte <= m_axi.wdata[7:0];
    end



    ////////////////////////////////////////////////////
    //DDR AXI interface
    assign ddr_axi_araddr = axi_araddr;
    assign ddr_axi_arburst = axi_arburst;
    assign ddr_axi_arcache = axi_arcache;
    assign ddr_axi_arid = axi_arid;
    assign ddr_axi_arlen = axi_arlen;
    assign axi_arready = ddr_axi_arready;
    assign ddr_axi_arsize = axi_arsize;
    assign ddr_axi_arvalid = axi_arvalid;

    assign ddr_axi_awaddr = axi_awaddr;
    assign ddr_axi_awburst = axi_awburst;
    assign ddr_axi_awcache = axi_awcache;
    assign ddr_axi_awid = axi_awid;
    assign ddr_axi_awlen =  axi_awlen;
    assign axi_awready = ddr_axi_awready;
    assign ddr_axi_awvalid = axi_awvalid;
    
    assign axi_bid = ddr_axi_bid;
    assign ddr_axi_bready = axi_bready;
    assign axi_bresp = ddr_axi_bresp;
    assign axi_bvalid = ddr_axi_bvalid;

    assign axi_rdata = ddr_axi_rdata;
    assign axi_rid = ddr_axi_rid;
    assign axi_rlast = ddr_axi_rlast;
    assign ddr_axi_rready = axi_rready;
    assign axi_rresp = ddr_axi_rresp;
    assign axi_rvalid = ddr_axi_rvalid;

    assign ddr_axi_wdata = axi_wdata;
    assign ddr_axi_wlast = axi_wlast;
    assign axi_wready = ddr_axi_wready;
    assign ddr_axi_wstrb = axi_wstrb;
    assign ddr_axi_wvalid = axi_wvalid;

    ////////////////////////////////////////////////////
    //Trace Interface
    localparam BENCHMARK_START_COLLECTION_NOP = 32'h00C00013;
    localparam BENCHMARK_END_COLLECTION_NOP = 32'h00D00013;

    logic start_collection;
    logic end_collection;

    //NOP detection
    always_comb begin
        start_collection = 0;
        end_collection = 0;
        foreach(retire_ports_valid[i]) begin
            start_collection |= retire_ports_valid[i] & (retire_ports_instruction[i] == BENCHMARK_START_COLLECTION_NOP);
            end_collection |= retire_ports_valid[i] & (retire_ports_instruction[i] == BENCHMARK_END_COLLECTION_NOP);
        end
    end

    //Hierarchy paths for major components 
    `define FETCH_P cpu.fetch_block
    `define ICACHE_P cpu.fetch_block.gen_fetch_icache.i_cache
    `define BRANCH_P cpu.branch_unit_block
    `define ISSUE_P cpu.decode_and_issue_block
    `define RENAME_P cpu.renamer_block
    `define METADATA_P cpu.id_block
    `define LS_P cpu.load_store_unit_block
    `define DIV_P cpu.gen_div.div_unit_block
    `define LSQ_P cpu.load_store_unit_block.lsq_block
    `define DCACHE_P cpu.load_store_unit_block.gen_ls_dcache.data_cache

    stats_t stats_enum;
    instruction_mix_stats_t instruction_mix_enum;
    localparam NUM_STATS = stats_enum.num();
    localparam NUM_INSTRUCTION_MIX_STATS = instruction_mix_enum.num();

    logic stats [NUM_STATS];
    logic is_mul [RETIRE_PORTS];
    logic is_div [RETIRE_PORTS];
    logic [NUM_INSTRUCTION_MIX_STATS-1:0] instruction_mix_stats [RETIRE_PORTS];

    logic icache_hit;
    logic icache_miss;
    logic iarb_stall;
    logic dcache_hit;
    logic dcache_miss;
    logic darb_stall;

    //Issue stalls
    logic base_no_instruction_stall;
    logic base_no_id_sub_stall;
    logic base_flush_sub_stall;
    logic base_unit_busy_stall;
    logic base_operands_stall;
    logic base_hold_stall;
    logic single_source_issue_stall;

    logic [3:0] stall_source_count;
    ///////////////

    //Issue phys_rd to unit mem
    //Used for determining what outputs an operand stall is waiting on
    logic [`ISSUE_P.NUM_UNITS-1:0] rd_addr_table [32];

    always_ff @(posedge clk) begin
        if (cpu.instruction_issued_with_rd)
            rd_addr_table[`ISSUE_P.issue.rd_addr] <= `ISSUE_P.unit_needed_issue_stage;
    end

    generate if (EXAMPLE_CONFIG.INCLUDE_ICACHE) begin
        assign icache_hit = `ICACHE_P.tag_hit;
        assign icache_miss = `ICACHE_P.second_cycle & ~`ICACHE_P.tag_hit;
        assign iarb_stall = `ICACHE_P.request_r & ~cpu.l1_request[L1_ICACHE_ID].ack;
    end endgenerate

    generate if (EXAMPLE_CONFIG.INCLUDE_DCACHE) begin
        assign dcache_hit = `DCACHE_P.load_hit;
        assign dcache_miss = `DCACHE_P.line_complete;
        assign darb_stall = cpu.l1_request[L1_DCACHE_ID].request & ~cpu.l1_request[L1_DCACHE_ID].ack;
    end endgenerate

    always_comb begin
        stats = '{default: '0};
        //Fetch
        stats[FETCH_EARLY_BR_CORRECTION_STAT] = `FETCH_P.early_branch_flush;
        stats[FETCH_SUB_UNIT_STALL_STAT] = `METADATA_P.pc_id_available & ~`FETCH_P.units_ready;
        stats[FETCH_ID_STALL_STAT] = ~`METADATA_P.pc_id_available;
        stats[FETCH_IC_HIT_STAT] = icache_hit;
        stats[FETCH_IC_MISS_STAT] = icache_miss;
        stats[FETCH_IC_ARB_STALL_STAT] = iarb_stall;

        //Branch predictor
        stats[FETCH_BP_BR_CORRECT_STAT] = `BRANCH_P.instruction_is_completing & ~`BRANCH_P.is_return_ex & ~`BRANCH_P.branch_flush;
        stats[FETCH_BP_BR_MISPREDICT_STAT] = `BRANCH_P.instruction_is_completing & ~`BRANCH_P.is_return_ex & `BRANCH_P.branch_flush;
        stats[FETCH_BP_RAS_CORRECT_STAT] = `BRANCH_P.instruction_is_completing & `BRANCH_P.is_return_ex & ~`BRANCH_P.branch_flush;
        stats[FETCH_BP_RAS_MISPREDICT_STAT] = `BRANCH_P.instruction_is_completing & `BRANCH_P.is_return_ex & `BRANCH_P.branch_flush;

        //Issue stalls
        base_no_instruction_stall = ~`ISSUE_P.issue.stage_valid | cpu.gc.fetch_flush;
            base_no_id_sub_stall = (`METADATA_P.post_issue_count == MAX_IDS);
            base_flush_sub_stall = cpu.gc.fetch_flush;
        base_unit_busy_stall = `ISSUE_P.issue.stage_valid & ~|`ISSUE_P.issue_ready;
        base_operands_stall = `ISSUE_P.issue.stage_valid & ~`ISSUE_P.operands_ready;
        base_hold_stall = `ISSUE_P.issue.stage_valid & (cpu.gc.issue_hold | `ISSUE_P.pre_issue_exception_pending);

        stall_source_count = 4'(base_no_instruction_stall) + 4'(base_unit_busy_stall) + 4'(base_operands_stall) + 4'(base_hold_stall);
        single_source_issue_stall = (stall_source_count == 1);

        //Issue stall determination
        stats[ISSUE_NO_INSTRUCTION_STAT] = base_no_instruction_stall & single_source_issue_stall;
        stats[ISSUE_NO_ID_STAT] = base_no_instruction_stall & base_no_id_sub_stall & single_source_issue_stall;
        stats[ISSUE_FLUSH_STAT] = base_no_instruction_stall & base_flush_sub_stall & single_source_issue_stall;
        stats[ISSUE_UNIT_BUSY_STAT] = base_unit_busy_stall & single_source_issue_stall;
        stats[ISSUE_OPERANDS_NOT_READY_STAT] = base_operands_stall & single_source_issue_stall;
        stats[ISSUE_HOLD_STAT] = base_hold_stall & single_source_issue_stall;
        stats[ISSUE_MULTI_SOURCE_STAT] = (base_no_instruction_stall | base_unit_busy_stall | base_operands_stall | base_hold_stall) & ~single_source_issue_stall;

        //Misc Issue stats
        stats[ISSUE_OPERAND_STALL_FOR_BRANCH_STAT] = stats[ISSUE_OPERANDS_NOT_READY_STAT] & `ISSUE_P.unit_needed_issue_stage[`ISSUE_P.UNIT_IDS.BR];
        stats[ISSUE_STORE_WITH_FORWARDED_DATA_STAT] = `ISSUE_P.issue_to[`ISSUE_P.UNIT_IDS.LS] & `LS_P.is_store_r & `LS_P.rs2_inuse;
        stats[ISSUE_DIVIDER_RESULT_REUSE_STAT] = `ISSUE_P.issue_to[`ISSUE_P.UNIT_IDS.DIV] & `DIV_P.div_op_reuse;

        //Issue Stall Source
        for (int i = 0; i < REGFILE_READ_PORTS; i++) begin
            stats[ISSUE_OPERAND_STALL_ON_LOAD_STAT] |= `ISSUE_P.issue.stage_valid & rd_addr_table[`ISSUE_P.issue_rs_addr[i]][`ISSUE_P.UNIT_IDS.LS] & `ISSUE_P.rs_conflict[i] ;
            stats[ISSUE_OPERAND_STALL_ON_MULTIPLY_STAT] |= EXAMPLE_CONFIG.INCLUDE_MUL & `ISSUE_P.issue.stage_valid & rd_addr_table[`ISSUE_P.issue_rs_addr[i]][`ISSUE_P.UNIT_IDS.MUL] & `ISSUE_P.rs_conflict[i] ;
            stats[ISSUE_OPERAND_STALL_ON_DIVIDE_STAT] |= EXAMPLE_CONFIG.INCLUDE_DIV & `ISSUE_P.issue.stage_valid & rd_addr_table[`ISSUE_P.issue_rs_addr[i]][`ISSUE_P.UNIT_IDS.DIV] & `ISSUE_P.rs_conflict[i] ;
        end

        //LS Stats
        stats[LSU_LOAD_BLOCKED_BY_STORE_STAT] = `LSQ_P.lq.valid & `LSQ_P.load_blocked;
        stats[LSU_SUB_UNIT_STALL_STAT] = (`LS_P.lsq.load_valid | `LS_P.lsq.store_valid) & ~`LS_P.sub_unit_ready;
        stats[LSU_DC_HIT_STAT] = dcache_hit;
        stats[LSU_DC_MISS_STAT] = dcache_miss;
        stats[LSU_DC_ARB_STALL_STAT] = darb_stall;

        //Retire Instruction Mix
        for (int i = 0; i < RETIRE_PORTS; i++) begin
                is_mul[i] = retire_ports_instruction[i][25] & ~retire_ports_instruction[i][14];
                is_div[i] = retire_ports_instruction[i][25] & retire_ports_instruction[i][14];
                instruction_mix_stats[i][ALU_STAT] = cpu.retire_port_valid[i] & (retire_ports_instruction[i][6:2] inside {ARITH_T, ARITH_IMM_T, AUIPC_T, LUI_T}) & ~(is_mul[i] | is_div[i]);
                instruction_mix_stats[i][BR_STAT] = cpu.retire_port_valid[i] & (retire_ports_instruction[i][6:2] inside {BRANCH_T, JAL_T, JALR_T});
                instruction_mix_stats[i][MUL_STAT] = cpu.retire_port_valid[i] & (retire_ports_instruction[i][6:2] inside {ARITH_T}) & is_mul[i];
                instruction_mix_stats[i][DIV_STAT] = cpu.retire_port_valid[i] & (retire_ports_instruction[i][6:2] inside {ARITH_T}) & is_div[i];
                instruction_mix_stats[i][LOAD_STAT] = cpu.retire_port_valid[i] & (retire_ports_instruction[i][6:2] inside {LOAD_T, AMO_T});// & retire_ports_instruction[i][14:12] inside {LS_B_fn3, L_BU_fn3};
                instruction_mix_stats[i][STORE_STAT] = cpu.retire_port_valid[i] & (retire_ports_instruction[i][6:2] inside {STORE_T, AMO_T});
                instruction_mix_stats[i][MISC_STAT] = cpu.retire_port_valid[i] & (retire_ports_instruction[i][6:2] inside {SYSTEM_T, FENCE_T});
        end
    end

    sim_stats #(.NUM_OF_STATS(NUM_STATS), .NUM_INSTRUCTION_MIX_STATS(NUM_INSTRUCTION_MIX_STATS)) stats_block (
        .clk (clk),
        .rst (rst),
        .start_collection (start_collection),
        .end_collection (end_collection),
        .stats (stats),
        .instruction_mix_stats (instruction_mix_stats),
        .retire_count (cpu.retire_count)
    );

    ////////////////////////////////////////////////////
    //Performs the lookups to provide the speculative architectural register file with
    //standard register names for simulation purposes
    logic [31:0][31:0] sim_registers_unamed_groups[EXAMPLE_CONFIG.NUM_WB_GROUPS];
    logic [31:0][31:0] sim_registers_unamed;

    simulation_named_regfile sim_register;
    typedef struct packed{
        phys_addr_t phys_addr;
        logic [$clog2(EXAMPLE_CONFIG.NUM_WB_GROUPS)-1:0] wb_group;
    } spec_table_t;
    spec_table_t translation [32];
    genvar i, j;
    generate  for (i = 0; i < 32; i++) begin : gen_reg_file_sim
        for (j = 0; j < EXAMPLE_CONFIG.NUM_WB_GROUPS; j++) begin
            if (FPGA_VENDOR == XILINX) begin
                assign translation[i] = cpu.renamer_block.spec_table_ram.xilinx_gen.ram[i];
                assign sim_registers_unamed_groups[j][i] = 
                cpu.register_file_block.register_file_gen[j].register_file_bank.xilinx_gen.ram[translation[i].phys_addr];
            end else if (FPGA_VENDOR == INTEL) begin
                assign translation[i] = cpu.renamer_block.spec_table_ram.intel_gen.lutrams[0].write_port.ram[i];
                assign sim_registers_unamed_groups[j][i] = 
                cpu.register_file_block.register_file_gen[j].register_file_bank.intel_gen.lutrams[0].write_port.ram[translation[i].phys_addr];
            end
        end
        assign sim_registers_unamed[31-i] = sim_registers_unamed_groups[translation[i].wb_group][i];
    end
    endgenerate

    assign NUM_RETIRE_PORTS = RETIRE_PORTS;
    generate for (genvar i = 0; i < RETIRE_PORTS; i++) begin
        assign retire_ports_pc[i] = cpu.id_block.pc_table[cpu.retire_ids[i]];
        assign retire_ports_instruction[i] = cpu.id_block.instruction_table[cpu.retire_ids[i]];
        assign retire_ports_valid[i] = cpu.retire_port_valid[i];
    end endgenerate

    assign store_queue_empty = cpu.load_store_status.sq_empty;

    ////////////////////////////////////////////////////
    //Assertion Binding

endmodule
