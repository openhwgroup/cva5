/*
 * Copyright © 2017 Eric Matthews, Chris Keilbart, Lesley Shannon
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
    import riscv_types::*;
    import cva5_types::*;

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

    //Peripheral busses
    local_memory_interface instruction_bram();
    local_memory_interface data_bram();
    axi_interface m_axi();
    avalon_interface m_avalon();
    wishbone_interface dwishbone();
    wishbone_interface iwishbone();

    //Primary memory busses
    axi_interface axi();
    mem_interface mem[0:0]();

    //Additional CPU signals
    interrupt_t s_interrupt;
    interrupt_t m_interrupt;
    logic[63:0] mtime;

    ////////////////////////////////////////////////////
    //CPU instantiation and mapping
    cva5 #(.CONFIG(EXAMPLE_CONFIG)) cpu(.mem(mem[0]), .*);
    axi_adapter #(.NUM_CORES(1)) arb(.mems(mem), .axi(axi), .*);

    //Local memory port mapping
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

    //Main memory port mapping
    assign ddr_axi_araddr = axi.araddr;
    assign ddr_axi_arburst = axi.arburst;
    assign ddr_axi_arcache = axi.arcache;
    assign ddr_axi_arid = axi.arid;
    assign ddr_axi_arlen = axi.arlen;
    assign axi.arready = ddr_axi_arready;
    assign ddr_axi_arsize = axi.arsize;
    assign ddr_axi_arvalid = axi.arvalid;

    assign ddr_axi_awaddr = axi.awaddr;
    assign ddr_axi_awburst = axi.awburst;
    assign ddr_axi_awcache = axi.awcache;
    assign ddr_axi_awid = axi.awid;
    assign ddr_axi_awlen =  axi.awlen;
    assign axi.awready = ddr_axi_awready;
    assign ddr_axi_awvalid = axi.awvalid;
    
    assign axi.bid = ddr_axi_bid;
    assign ddr_axi_bready = axi.bready;
    assign axi.bresp = ddr_axi_bresp;
    assign axi.bvalid = ddr_axi_bvalid;

    assign axi.rdata = ddr_axi_rdata;
    assign axi.rid = ddr_axi_rid;
    assign axi.rlast = ddr_axi_rlast;
    assign ddr_axi_rready = axi.rready;
    assign axi.rresp = ddr_axi_rresp;
    assign axi.rvalid = ddr_axi_rvalid;

    assign ddr_axi_wdata = axi.wdata;
    assign ddr_axi_wlast = axi.wlast;
    assign axi.wready = ddr_axi_wready;
    assign ddr_axi_wstrb = axi.wstrb;
    assign ddr_axi_wvalid = axi.wvalid;

    //Other CPU signals
    assign s_interrupt = '{default: 0};
    assign m_interrupt = '{default: 0};

    always_ff @(posedge clk) begin
        if (rst)
            mtime <= '0;
        else
            mtime <= mtime + 1;
    end

    //Simulate a UART on the peripheral AXI bus
    //Write channels
    always_ff @(posedge clk) begin
        if (rst) begin
            m_axi.awready <= 1;
            m_axi.wready <= 0;
            m_axi.bvalid <= 0;
            write_uart <= 0;
        end
        else begin
            write_uart <= 0;
            if (m_axi.awvalid & m_axi.awready) begin
                m_axi.awready <= 0;
                m_axi.wready <= 1;
            end
            else if (m_axi.wvalid & m_axi.wready) begin
                m_axi.wready <= 0;
                m_axi.bvalid <= 1;
                write_uart <= 1;
            end
            else if (m_axi.bvalid & m_axi.bready) begin
                m_axi.bvalid <= 0;
                m_axi.awready <= 1;
            end
        end
        uart_byte <= m_axi.wdata[7:0];
    end

    //Read channels
    assign m_axi.rdata = 32'hFFFFFF21;
    always_ff @(posedge clk) begin
        if (rst) begin
            m_axi.arready <= 1;
            m_axi.rvalid <= 0;
        end
        else begin
            if (m_axi.arvalid & m_axi.arready) begin
                m_axi.arready <= 0;
                m_axi.rvalid <= 1;
            end
            else if (m_axi.rvalid & m_axi.rready) begin
                m_axi.rvalid <= 0;
                m_axi.arready <= 1;
            end
        end
    end


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

    //Issue rd_addr to unit mem
    //Used for determining what outputs an operand stall is waiting on
    logic [MAX_NUM_UNITS-1:0] rd_addr_table [32];

    always_ff @(posedge clk) begin
        if (cpu.instruction_issued_with_rd)
            rd_addr_table[`ISSUE_P.issue.rd_addr] <= `ISSUE_P.unit_needed_issue_stage;
    end

    generate if (EXAMPLE_CONFIG.INCLUDE_ICACHE) begin
        assign icache_hit = `ICACHE_P.tag_hit;
        assign icache_miss = `ICACHE_P.second_cycle & ~`ICACHE_P.tag_hit;
        assign iarb_stall = `ICACHE_P.request_r & ~cpu.icache_mem.ack;
    end endgenerate

    generate if (EXAMPLE_CONFIG.INCLUDE_DCACHE) begin
        //Depends on data cache type; not enabled for now
        // assign dcache_hit = `DCACHE_P.load_hit;
        // assign dcache_miss = `DCACHE_P.line_complete;
        // assign darb_stall = cpu.dcache_mem.request & ~cpu.dcache_mem.ack;
    end endgenerate

    logic [MAX_NUM_UNITS-1:0] unit_ready;
    generate for (i=0; i<MAX_NUM_UNITS; i++)
        assign unit_ready[i] = cpu.unit_issue[i].ready;
    endgenerate

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
        base_unit_busy_stall = `ISSUE_P.issue.stage_valid & ~|(`ISSUE_P.unit_needed_issue_stage & unit_ready);
        base_operands_stall = `ISSUE_P.issue.stage_valid & ~(&`ISSUE_P.operand_ready);
        base_hold_stall = `ISSUE_P.issue.stage_valid & `ISSUE_P.issue_hold;

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
        stats[ISSUE_OPERAND_STALL_FOR_BRANCH_STAT] = stats[ISSUE_OPERANDS_NOT_READY_STAT] & `ISSUE_P.unit_needed_issue_stage[BR_ID];
        stats[ISSUE_STORE_WITH_FORWARDED_DATA_STAT] = `ISSUE_P.issue_to[LS_ID] & `LS_P.issue_attr.is_store & `LS_P.rs2_inuse;
        stats[ISSUE_DIVIDER_RESULT_REUSE_STAT] = `ISSUE_P.issue_to[DIV_ID] & `DIV_P.div_op_reuse;

        //Issue Stall Source
        for (int i = 0; i < REGFILE_READ_PORTS; i++) begin
            stats[ISSUE_OPERAND_STALL_ON_LOAD_STAT] |= `ISSUE_P.issue.stage_valid & rd_addr_table[`ISSUE_P.issue_rs_addr[i]][LS_ID] & ~`ISSUE_P.operand_ready[i] ;
            stats[ISSUE_OPERAND_STALL_ON_MULTIPLY_STAT] |= EXAMPLE_CONFIG.INCLUDE_UNIT.MUL & `ISSUE_P.issue.stage_valid & rd_addr_table[`ISSUE_P.issue_rs_addr[i]][MUL_ID] & ~`ISSUE_P.operand_ready[i] ;
            stats[ISSUE_OPERAND_STALL_ON_DIVIDE_STAT] |= EXAMPLE_CONFIG.INCLUDE_UNIT.DIV & `ISSUE_P.issue.stage_valid & rd_addr_table[`ISSUE_P.issue_rs_addr[i]][DIV_ID] & ~`ISSUE_P.operand_ready[i] ;
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
            instruction_mix_stats[i][LOAD_STAT] = cpu.retire_port_valid[i] & (retire_ports_instruction[i][6:2] inside {LOAD_T, FPU_LOAD_T, AMO_T});// & retire_ports_instruction[i][14:12] inside {LS_B_fn3, L_BU_fn3};
            instruction_mix_stats[i][STORE_STAT] = cpu.retire_port_valid[i] & (retire_ports_instruction[i][6:2] inside {STORE_T, FPU_STORE_T, AMO_T});
            instruction_mix_stats[i][FPU_STAT] = cpu.retire_port_valid[i] & (retire_ports_instruction[i][6:2] inside {FPU_MADD_T, FPU_MSUB_T, FPU_NMSUB_T, FPU_NMADD_T, FPU_OP_T});
            instruction_mix_stats[i][MISC_STAT] = cpu.retire_port_valid[i] & (retire_ports_instruction[i][6:2] inside {SYSTEM_T, FENCE_T});
        end
    end

    sim_stats #(.NUM_OF_STATS(NUM_STATS), .NUM_INSTRUCTION_MIX_STATS(NUM_INSTRUCTION_MIX_STATS)) stats_block (
        .start_collection(start_collection),
        .end_collection(end_collection),
        .stats(stats),
        .instruction_mix_stats(instruction_mix_stats),
        .retire_count(cpu.retire_count),
    .*);

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

    //FPU
    logic [31:0][FLEN-1:0] fp_sim_registers_unamed_groups[2];
    logic [31:0][FLEN-1:0] fp_sim_registers_unamed;
    fp_simulation_named_regfile fp_sim_register;
    typedef struct packed{
        phys_addr_t fp_phys_addr;
        logic fp_wb_group;
    } fp_spec_table_t;
    fp_spec_table_t fp_translation [32];

    generate if (EXAMPLE_CONFIG.INCLUDE_UNIT.FPU) begin : gen_fp_reg_file_sim
        for (i = 0; i < 32; i++) begin
            for (j = 0; j < 2; j++) begin
                if (FPGA_VENDOR == XILINX) begin
                    assign fp_translation[i] = cpu.gen_fpu.fp_renamer_block.spec_table_ram.xilinx_gen.ram[i];
                    assign fp_sim_registers_unamed_groups[j][i] = cpu.gen_fpu.fp_register_file_block.register_file_gen[j].register_file_bank.xilinx_gen.ram[fp_translation[i].fp_phys_addr];
                end else if (FPGA_VENDOR == INTEL) begin
                    assign fp_translation[i] = cpu.gen_fpu.fp_renamer_block.spec_table_ram.intel_gen.lutrams[0].write_port.ram[i];
                    assign fp_sim_registers_unamed_groups[j][i] = cpu.gen_fpu.fp_register_file_block.register_file_gen[j].register_file_bank.intel_gen.lutrams[0].write_port.ram[fp_translation[i].fp_phys_addr];
                end
            end
            assign fp_sim_registers_unamed[31-i] = fp_sim_registers_unamed_groups[fp_translation[i].fp_wb_group][i];
        end
    end
    endgenerate

    assign NUM_RETIRE_PORTS = RETIRE_PORTS;
    generate for (genvar i = 0; i < RETIRE_PORTS; i++) begin
        assign retire_ports_pc[i] = cpu.id_block.pc_table.ram[cpu.retire_ids[i]];
        assign retire_ports_instruction[i] = cpu.id_block.instruction_table.ram[cpu.retire_ids[i]];
        assign retire_ports_valid[i] = cpu.retire_port_valid[i];
    end endgenerate

    assign store_queue_empty = ~cpu.load_store_status.outstanding_store;

endmodule
