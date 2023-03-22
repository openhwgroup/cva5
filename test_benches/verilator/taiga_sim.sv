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

module taiga_sim 

    import taiga_config::*;
    import l2_config_and_types::*;
    import riscv_types::*;
    import taiga_types::*;

    # (
        parameter MEMORY_FILE = "/home/ematthew/Research/RISCV/software/riscv-tools/riscv-tests/benchmarks/dhrystone.riscv.hw_init", //change this to appropriate location "/home/ematthew/Downloads/dhrystone.riscv.sim_init"
        parameter INTERFACE_FLEN = 64
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

        output logic [28:0] data_bram_addr,
        output logic [1:0] data_bram_we, // <= {is_float, we} 
        output logic data_bram_en,
        output logic [3:0] data_bram_be,
        output logic [INTERFACE_FLEN-1:0] data_bram_data_in,
        input logic [INTERFACE_FLEN-1:0] data_bram_data_out,

        //Used by verilator
        output logic write_uart,
        output logic [7:0] uart_byte,

        //Trace Interface
        output integer NUM_RETIRE_PORTS,
        output logic [31:0] retire_ports_instruction [RETIRE_PORTS],
        output logic [31:0] retire_ports_pc [RETIRE_PORTS],
        output logic retire_ports_valid [RETIRE_PORTS],
        output logic store_queue_empty,
        output logic load_store_idle,

        output logic instruction_issued,
        output logic taiga_events [0:$bits(taiga_trace_events_t)-1],
        output logic [31:0] instruction_pc_dec,
        input logic [63:0] debug_instructions,
        output logic [31:0] instruction_data_dec,
        output logic fp_taiga_events [0:$bits(fp_taiga_trace_events_t)-1],
        output logic LargeSigTrace [0:$bits(LargeSigTrace_t)-1]
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
    wishbone_interface m_wishbone();

    trace_outputs_t tr;
    fp_trace_outputs_t fp_tr;

    l2_requester_interface l2[L2_NUM_PORTS-1:0]();
    l2_memory_interface mem();

    local_memory_interface instruction_bram();
    fp_local_memory_interface data_bram();

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
    assign data_bram_we = data_bram.we;
    assign data_bram_data_in = data_bram.data_in;
    assign data_bram.data_out = data_bram_data_out;

    taiga #(.CONFIG(EXAMPLE_CONFIG)) cpu(.*, .l2(l2[0]));

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
    assign instruction_pc_dec = tr.instruction_pc_dec;
    assign instruction_data_dec = tr.instruction_data_dec;
    assign instruction_issued = tr.events.instruction_issued_dec;
    logic [$bits(taiga_trace_events_t)-1:0] taiga_events_packed;
    assign taiga_events_packed = tr.events;
    always_comb begin
        foreach(taiga_events_packed[i])
            taiga_events[$bits(taiga_trace_events_t)-1-i] = taiga_events_packed[i];
    end

    logic [$bits(fp_taiga_trace_events_t)-1:0] fp_taiga_events_packed;
    logic [$bits(LargeSigTrace_t)-1:0] LargeSigTrace_packed;
    assign fp_taiga_events_packed = fp_tr.events;
    assign LargeSigTrace_packed = fp_tr.sigs;
    always_comb begin
       foreach(fp_taiga_events_packed[i])
         fp_taiga_events[$bits(fp_taiga_trace_events_t)-1-i] = fp_taiga_events_packed[i];

       foreach(LargeSigTrace_packed[i])
         LargeSigTrace[$bits(LargeSigTrace_t)-1-i] = LargeSigTrace_packed[i];
    end 

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
    generate  for (i = 0; i < 32; i++) begin
        for (j = 0; j < EXAMPLE_CONFIG.NUM_WB_GROUPS; j++) begin
            if (FPGA_VENDOR == XILINX)
                assign translation[i] = cpu.renamer_block.spec_table_ram.xilinx_gen.ram[i];
            else if (FPGA_VENDOR == INTEL)
                assign translation[i] = cpu.renamer_block.spec_table_ram.intel_gen.lutrams[0].write_port.ram[i];

            assign sim_registers_unamed_groups[j][i] = 
            cpu.register_file_block.register_file_gen[j].reg_group.register_file_bank[translation[i].phys_addr];
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

    assign store_queue_empty = cpu.sq_empty;
    assign load_store_idle = cpu.load_store_idle;


    ////////////////////////////////////////////////////
    //FPU Tracer 
    generate if (ENABLE_TRACE_INTERFACE & INCLUDE_FPU) begin : fpu_tracer
        logic fp_instruction_issued_dec;
        logic fp_operand_stall;
        logic fp_unit_stall;
        logic fp_no_id_stall;
        logic fp_no_instruction_stall;
        logic fp_other_stall;
        logic fls_operand_stall;
        logic fmadd_operand_stall;
        logic fadd_operand_stall;
        logic fmul_operand_stall;
        logic fdiv_operand_stall;
        logic fsqrt_operand_stall;
        logic fcmp_operand_stall;
        logic fsign_inject_operand_stall;
        logic fclass_operand_stall;
        logic fcvt_operand_stall;
        logic fp_load_op;
        logic fp_store_op;
        logic fp_fmadd_op;
        logic fp_add_op;
        logic fp_mul_op;
        logic fp_div_op;
        logic fp_sqrt_op;
        logic fp_cvt_op;
        logic fp_cmp_op;
        logic fp_minmax_op;
        logic fp_class_op;
        logic fp_sign_inject_op;
        logic operand_stall_due_to_fls;
        logic operand_stall_due_to_fmadd;
        logic operand_stall_due_to_fdiv_sqrt;
        logic operand_stall_due_to_wb2fp;
        logic fmadd_wb_stall;
        logic fmul_wb_stall;
        logic fdiv_sqrt_wb_stall;
        logic wb2fp_wb_stall;
        logic fmadd_stall_due_to_fmadd;
        logic fmadd_operand_stall_rs1;
        logic fmadd_operand_stall_rs2;
        logic fmadd_operand_stall_rs3;
        logic fadd_operand_stall_rs1;
        logic fadd_operand_stall_rs2;
        logic fmul_operand_stall_rs1;
        logic fmul_operand_stall_rs2;
        logic fadd_stall_due_to_fmadd; 
        logic rs1_subnormal;
        logic rs2_subnormal;
        logic rs3_subnormal;
        logic rd_subnormal;
        logic wb_round_overflow;
        logic roundup;
        logic overflowExp;
        logic underflowExp;
        int in_flight_ids;

        logic rs1_conflict, rs2_conflict, rs3_conflict;
        //logic uses_rs1, uses_rs2, uses_rs3;

        //Operand Stall Source Tracking
        logic [cpu.FP_NUM_UNITS:0] stall_unit_onehot [2:0];
        logic [cpu.FP_NUM_UNITS:0] register_unit_id_table [63:0]; //maps each register and its result-producing issue-side unit {fls, fpu_issue_to}
        //Writeback Stall Tracking
        logic [cpu.FP_NUM_WB_UNITS-1:0] fp_units_pending_wb;
        assign fp_units_pending_wb = cpu.fp_writeback_block.unit_done[0] ^ cpu.fp_writeback_block.unit_ack[0];

        //the table holds, for each register, the unit_id (onehot) that will write to it
        //the three unit_ids are read using the phys_rs_addr, and if conflict exists on any of the rs_addr, check if the unit_id matches that of the units, if so the unit caused the operand stall
        logic [4:0] debug;
        logic [4:0] debug_50;
        assign debug_50 = register_unit_id_table[50];
        assign debug = {cpu.unit_issue[cpu.UNIT_IDS.LS].new_request&cpu.issue.is_float&cpu.ls_inputs.load, cpu.decode_and_issue_block.issue_to[cpu.TOTAL_NUM_UNITS-1-:cpu.FP_NUM_UNITS]};

        //writeback stall source tracking
        logic [3:0] unit_done_r, unit_done_r_r;
        always_ff @ (posedge clk) begin
            if (cpu.decode_and_issue_block.fp_instruction_issued_with_rd) begin
                register_unit_id_table[cpu.issue.fp_phys_rd_addr] <= {cpu.unit_issue[cpu.UNIT_IDS.LS].new_request&cpu.issue.is_float&cpu.ls_inputs.load, cpu.decode_and_issue_block.issue_to[cpu.TOTAL_NUM_UNITS-1-:cpu.FP_NUM_UNITS]};
            end

            if (cpu.fp_commit_packet[0].valid) begin
                register_unit_id_table[cpu.fp_commit_packet[0].phys_addr] <= 0;
            end

            unit_done_r <= cpu.fpu_block.fpu_block.norm_round_inst.unit_done[0];
            unit_done_r_r <= unit_done_r;

            //if (cpu.decode_and_issue_block.instruction_issued & (uses_rs1 | uses_rs2 | uses_rs3) & ~fp_store_op)
                //$display("pc: 0x%h, rs1: 0x%h, rs2: 0x%h, rs3: 0x%h, int_rs1: 0x%h", cpu.decode_and_issue_block.issue.pc, cpu.fp_pre_processing_packet.rs1,cpu.fp_pre_processing_packet.rs2, cpu.fp_pre_processing_packet.rs3, cpu.fp_pre_processing_packet.int_rs1);
        end

        always_comb begin
            stall_unit_onehot[2] = register_unit_id_table[cpu.issue.fp_phys_rs_addr[RS3]]; 
            stall_unit_onehot[1] = register_unit_id_table[cpu.issue.fp_phys_rs_addr[RS2]]; 
            stall_unit_onehot[0] = register_unit_id_table[cpu.issue.fp_phys_rs_addr[RS1]]; 
        end

        //operand stall source tracking signals
        assign rs1_conflict = cpu.decode_and_issue_block.fp_decode_and_issue_block.fp_decode_and_issue_block.rs1_conflict;
        assign rs2_conflict = cpu.decode_and_issue_block.fp_decode_and_issue_block.fp_decode_and_issue_block.rs2_conflict;
        assign rs3_conflict = cpu.decode_and_issue_block.fp_decode_and_issue_block.fp_decode_and_issue_block.rs3_conflict;
        //assign uses_rs1 = cpu.issue.fp_uses_rs1;
        //assign uses_rs2 = cpu.issue.fp_uses_rs2;
        //assign uses_rs3 = cpu.issue.fp_uses_rs3;

        ////////////////////////////////////////////////////
        //Stall 
        always_comb begin
            //stall
            fp_instruction_issued_dec = cpu.instruction_issued & cpu.issue.is_float;
            fp_operand_stall        = cpu.issue.stage_valid & ~cpu.gc.fetch_flush & ~cpu.gc.issue_hold & ~cpu.decode_and_issue_block.fp_operands_ready & |cpu.decode_and_issue_block.issue_ready;
            fp_no_id_stall          = (~cpu.issue.stage_valid & ~cpu.pc_id_available & ~cpu.gc.fetch_flush); //All instructions in execution pipeline
            fp_unit_stall           = cpu.decode_and_issue_block.issue_valid & cpu.issue.is_float & ~cpu.gc.fetch_flush & ~|cpu.decode_and_issue_block.issue_ready;
            fp_no_instruction_stall = (~fp_no_id_stall & ~cpu.issue.stage_valid) | cpu.gc.fetch_flush;
            fp_other_stall          = cpu.issue.is_float & cpu.issue.stage_valid & ~cpu.instruction_issued & ~(fp_operand_stall | fp_unit_stall  | fp_no_id_stall | fp_no_instruction_stall);

            fls_operand_stall   = fp_operand_stall & cpu.decode_and_issue_block.unit_needed_issue_stage[cpu.UNIT_IDS.LS] & cpu.issue.is_float;
            fmadd_operand_stall = fp_operand_stall & cpu.decode_and_issue_block.unit_needed_issue_stage[cpu.NUM_UNITS+cpu.FMADD_UNIT_ID] & cpu.fpu_block.fpu_block.fp_pre_processing_inst.is_fma;
            fadd_operand_stall  = fp_operand_stall & cpu.decode_and_issue_block.unit_needed_issue_stage[cpu.NUM_UNITS+cpu.FMADD_UNIT_ID] & cpu.fpu_block.fpu_block.fp_pre_processing_inst.is_fadd;
            fmul_operand_stall  = fp_operand_stall & cpu.decode_and_issue_block.unit_needed_issue_stage[cpu.NUM_UNITS+cpu.FMADD_UNIT_ID] & cpu.fpu_block.fpu_block.fp_pre_processing_inst.is_fmul;
            //fdiv_operand_stall  = fp_operand_stall & cpu.decode_and_issue_block.unit_needed_issue_stage[cpu.NUM_UNITS+cpu.FDIV_SQRT_UNIT_ID] & cpu.issue.fn7 == FDIV;
            //fsqrt_operand_stall = fp_operand_stall & cpu.decode_and_issue_block.unit_needed_issue_stage[cpu.NUM_UNITS+cpu.FDIV_SQRT_UNIT_ID] & cpu.issue.fn7 == FSQRT;
            //fcmp_operand_stall  = fp_operand_stall & ((cpu.decode_and_issue_block.unit_needed_issue_stage[cpu.NUM_UNITS+cpu.MISC_WB2INT_UNIT_ID] & cpu.decode_and_issue_block.fp_decode_and_issue_block.fp_decode_and_issue_block.is_fcmp_r) | (cpu.decode_and_issue_block.unit_needed_issue_stage[cpu.NUM_UNITS+cpu.MISC_WB2FP_UNIT_ID] & cpu.decode_and_issue_block.fp_decode_and_issue_block.fp_decode_and_issue_block.is_minmax_r));
            //fsign_inject_operand_stall = fp_operand_stall & cpu.decode_and_issue_block.unit_needed_issue_stage[cpu.NUM_UNITS+cpu.MISC_WB2FP_UNIT_ID] & cpu.decode_and_issue_block.fp_decode_and_issue_block.fp_decode_and_issue_block.is_sign_inj_r;
            //fclass_operand_stall       = fp_operand_stall & cpu.decode_and_issue_block.unit_needed_issue_stage[cpu.NUM_UNITS+cpu.MISC_WB2INT_UNIT_ID] & cpu.decode_and_issue_block.fp_decode_and_issue_block.fp_decode_and_issue_block.is_class_r;
            //fcvt_operand_stall         = (fp_operand_stall & cpu.decode_and_issue_block.unit_needed_issue_stage[cpu.NUM_UNITS+cpu.FP_UNIT_IDS.MISC_WB2INT] & cpu.decode_and_issue_block.fp_decode_and_issue_block.fp_decode_and_issue_block.is_f2i_r);// | (fp_operand_stall & cpu.decode_and_issue_block.unit_needed_issue_stage[cpu.NUM_UNITS+cpu.MISC_WB2FP_UNIT_ID] & cpu.decode_and_issue_block.fp_decode_and_issue_block.fp_decode_and_issue_block.is_i2f_r);

            //instruction mix
            fp_load_op  = cpu.unit_issue[cpu.UNIT_IDS.LS].new_request & cpu.issue.is_float & cpu.ls_inputs.load;
            fp_store_op = cpu.unit_issue[cpu.UNIT_IDS.LS].new_request & cpu.issue.is_float & cpu.ls_inputs.store;
            fp_fmadd_op = cpu.fpu_block.fpu_block.fp_madd_inst.mul_issue.new_request & cpu.fpu_block.fpu_block.fp_madd_inst.fp_madd_inputs.instruction[2];
            fp_add_op   = cpu.fpu_block.fpu_block.fp_madd_inst.fp_add_inputs_fifo.push;// & cpu.fp_madd_inputs.instruction[1];
            fp_mul_op   = cpu.fpu_block.fpu_block.fp_madd_inst.mul_issue.new_request & cpu.fpu_block.fpu_block.fp_madd_inst.fp_madd_inputs.instruction[0];
            fp_div_op   = cpu.fpu_block.fpu_block.div_sqrt_inst.div_issue.new_request;
            fp_sqrt_op  = cpu.fpu_block.fpu_block.div_sqrt_inst.sqrt_issue.new_request;
            fp_cvt_op   = cpu.fpu_block.fpu_block.wb2fp_misc_inst.i2f_issue.new_request | cpu.fpu_block.fpu_block.wb2int_misc_inst.f2i_issue.new_request;
            fp_cmp_op         = cpu.fpu_block.fpu_block.wb2int_misc_inst.cmp_issue.new_request;
            fp_minmax_op      = cpu.fpu_block.fpu_block.wb2fp_misc_inst.minmax_issue.new_request;
            fp_class_op       = cpu.fpu_block.fpu_block.wb2int_misc_inst.class_issue.new_request;
            fp_sign_inject_op = cpu.fpu_block.fpu_block.wb2fp_misc_inst.sign_inj_issue.new_request;

            //unit stall
            operand_stall_due_to_fls = ((stall_unit_onehot[RS3][cpu.FP_NUM_UNITS] & rs3_conflict) | (stall_unit_onehot[RS2][cpu.FP_NUM_UNITS] & rs2_conflict) | (stall_unit_onehot[RS1][cpu.FP_NUM_UNITS] & rs1_conflict)) & fp_operand_stall;
            operand_stall_due_to_fmadd = ((stall_unit_onehot[RS3][cpu.FMADD_UNIT_ID] & rs3_conflict) | (stall_unit_onehot[RS2][cpu.FMADD_UNIT_ID] & rs2_conflict) | (stall_unit_onehot[RS1][cpu.FMADD_UNIT_ID] & rs1_conflict)) & fp_operand_stall;
            operand_stall_due_to_fdiv_sqrt = ((stall_unit_onehot[RS3][cpu.FDIV_SQRT_UNIT_ID] & rs3_conflict) | (stall_unit_onehot[RS2][cpu.FDIV_SQRT_UNIT_ID] & rs2_conflict) | (stall_unit_onehot[RS1][cpu.FDIV_SQRT_UNIT_ID] & rs1_conflict)) & fp_operand_stall;
            operand_stall_due_to_wb2fp = ((stall_unit_onehot[RS3][cpu.MISC_WB2FP_UNIT_ID] & rs3_conflict) | (stall_unit_onehot[RS2][cpu.MISC_WB2FP_UNIT_ID] & rs2_conflict) | (stall_unit_onehot[RS1][cpu.MISC_WB2FP_UNIT_ID] & rs1_conflict)) & fp_operand_stall;

            //writeback stall
            fmadd_wb_stall           = fp_units_pending_wb[cpu.FP_ARITH_WB_ID] & unit_done_r_r[cpu.FMADD_WB_ID];
            fmul_wb_stall            = fp_units_pending_wb[cpu.FP_ARITH_WB_ID] & unit_done_r_r[cpu.FMUL_WB_ID];
            fdiv_sqrt_wb_stall       = fp_units_pending_wb[cpu.FP_ARITH_WB_ID] & unit_done_r_r[cpu.FDIV_SQRT_WB_ID];
            wb2fp_wb_stall           = fp_units_pending_wb[cpu.FP_ARITH_WB_ID] & unit_done_r_r[cpu.MISC_WB2FP_WB_ID];

            fmadd_stall_due_to_fmadd = operand_stall_due_to_fmadd & (fmadd_operand_stall | fmul_operand_stall | fadd_operand_stall);
            fmadd_operand_stall_rs1  = fmadd_operand_stall & rs1_conflict;
            fmadd_operand_stall_rs2  = fmadd_operand_stall & rs2_conflict;
            fmadd_operand_stall_rs3  = fmadd_operand_stall & rs3_conflict;
            fadd_operand_stall_rs1   = fadd_operand_stall & rs1_conflict;
            fadd_operand_stall_rs2   = fadd_operand_stall & rs2_conflict;
            fmul_operand_stall_rs1   = fmul_operand_stall & rs1_conflict;
            fmul_operand_stall_rs2   = fmul_operand_stall & rs2_conflict;
            fadd_stall_due_to_fmadd  = cpu.fpu_block.fpu_block.fp_madd_inst.add_issue.new_request & ~cpu.fpu_block.fpu_block.fp_madd_inst.fp_add_inputs_fifo.pop & cpu.fpu_block.fpu_block.fp_madd_inst.fp_add_inputs_fifo.valid; //fadd input fifo not issued though valid
            //rs1_subnormal = cpu.instruction_issued & uses_rs1 & ~cpu.decode_and_issue_block.fp_decode_and_issue_block.fp_decode_and_issue_block.hidden_bit[RS1] & ~cpu.decode_and_issue_block.fp_decode_and_issue_block.fp_decode_and_issue_block.is_zero[RS1];
            //rs2_subnormal = cpu.instruction_issued & uses_rs2 & ~cpu.decode_and_issue_block.fp_decode_and_issue_block.fp_decode_and_issue_block.hidden_bit[RS2] & ~cpu.decode_and_issue_block.fp_decode_and_issue_block.fp_decode_and_issue_block.is_zero[RS2];
            //rs3_subnormal = cpu.instruction_issued & uses_rs3 & ~cpu.decode_and_issue_block.fp_decode_and_issue_block.fp_decode_and_issue_block.hidden_bit[RS3] & ~cpu.decode_and_issue_block.fp_decode_and_issue_block.fp_decode_and_issue_block.is_zero[RS3];
            rd_subnormal = cpu.fp_commit_packet[0].valid & ~(|cpu.fp_commit_packet[0].data[FLEN-2-:EXPO_WIDTH]) & |cpu.fp_commit_packet[0].data[0+:FRAC_WIDTH];
            wb_round_overflow = cpu.fpu_block.fpu_block.norm_round_inst.frac_overflow & cpu.fpu_block.fpu_block.norm_round_inst.round_packet_r.valid;
            roundup = cpu.fpu_block.fpu_block.norm_round_inst.roundup & cpu.fpu_block.fpu_block.norm_round_inst.round_packet_r.valid;
            overflowExp = cpu.fpu_block.fpu_block.norm_round_inst.overflowExp & cpu.fpu_block.fpu_block.norm_round_inst.round_packet_r.valid;
            underflowExp = cpu.fpu_block.fpu_block.norm_round_inst.underflowExp & cpu.fpu_block.fpu_block.norm_round_inst.round_packet_r.valid;
            in_flight_ids = cpu.id_block.inflight_count[LOG2_MAX_IDS] ? 32'(MAX_IDS) : 32'(cpu.id_block.inflight_count[LOG2_MAX_IDS-1:0]);
        end

        always_ff @ (posedge clk) begin
            fp_tr.events.fp_instruction_issued_dec <= fp_instruction_issued_dec;
            fp_tr.events.fp_operand_stall <= fp_operand_stall;
            fp_tr.events.fp_unit_stall <= fp_unit_stall;
            fp_tr.events.fp_no_id_stall <= fp_no_id_stall;
            fp_tr.events.fp_no_instruction_stall <= fp_no_instruction_stall;
            fp_tr.events.fp_other_stall <= fp_other_stall;
            fp_tr.events.fls_operand_stall <= fls_operand_stall;
            fp_tr.events.fmadd_operand_stall <= fmadd_operand_stall;
            fp_tr.events.fadd_operand_stall <= fadd_operand_stall;
            fp_tr.events.fmul_operand_stall <= fmul_operand_stall;
            fp_tr.events.fdiv_operand_stall <= fdiv_operand_stall;
            fp_tr.events.fsqrt_operand_stall <= fsqrt_operand_stall;
            fp_tr.events.fcmp_operand_stall <= fcmp_operand_stall;
            fp_tr.events.fsign_inject_operand_stall <= fsign_inject_operand_stall;
            fp_tr.events.fclass_operand_stall <= fclass_operand_stall;
            fp_tr.events.fcvt_operand_stall <= fcvt_operand_stall;
            fp_tr.events.fp_load_op <= fp_load_op;
            fp_tr.events.fp_store_op <= fp_store_op;
            fp_tr.events.fp_fmadd_op <= fp_fmadd_op;
            fp_tr.events.fp_add_op <= fp_add_op;
            fp_tr.events.fp_mul_op <= fp_mul_op;
            fp_tr.events.fp_div_op <= fp_div_op;
            fp_tr.events.fp_sqrt_op <= fp_sqrt_op;
            fp_tr.events.fp_cvt_op <= fp_cvt_op;
            fp_tr.events.fp_cmp_op <= fp_cmp_op;
            fp_tr.events.fp_minmax_op <= fp_minmax_op;
            fp_tr.events.fp_class_op <= fp_class_op;
            fp_tr.events.fp_sign_inject_op <= fp_sign_inject_op;
            fp_tr.events.operand_stall_due_to_fls <= operand_stall_due_to_fls;
            fp_tr.events.operand_stall_due_to_fmadd <= operand_stall_due_to_fmadd;
            fp_tr.events.operand_stall_due_to_fdiv_sqrt <= operand_stall_due_to_fdiv_sqrt;
            fp_tr.events.operand_stall_due_to_wb2fp <= operand_stall_due_to_wb2fp;
            fp_tr.events.fmadd_wb_stall <= fmadd_wb_stall;
            fp_tr.events.fmul_wb_stall <= fmul_wb_stall;
            fp_tr.events.fdiv_sqrt_wb_stall <= fdiv_sqrt_wb_stall;
            fp_tr.events.wb2fp_wb_stall <= wb2fp_wb_stall;
            fp_tr.events.fmadd_stall_due_to_fmadd <= fmadd_stall_due_to_fmadd;
            fp_tr.events.fmadd_operand_stall_rs1 <= fmadd_operand_stall_rs1;
            fp_tr.events.fmadd_operand_stall_rs2 <= fmadd_operand_stall_rs2;
            fp_tr.events.fmadd_operand_stall_rs3 <= fmadd_operand_stall_rs3;
            fp_tr.events.fadd_operand_stall_rs1 <= fadd_operand_stall_rs1;
            fp_tr.events.fadd_operand_stall_rs2 <= fadd_operand_stall_rs2;
            fp_tr.events.fmul_operand_stall_rs1 <= fmul_operand_stall_rs1;
            fp_tr.events.fmul_operand_stall_rs2 <= fmul_operand_stall_rs2;
            fp_tr.events.fadd_stall_due_to_fmadd <= fadd_stall_due_to_fmadd;
            fp_tr.events.rs1_subnormal <= rs1_subnormal;
            fp_tr.events.rs2_subnormal <= rs2_subnormal;
            fp_tr.events.rs3_subnormal <= rs3_subnormal;
            fp_tr.events.rd_subnormal <= rd_subnormal;
            fp_tr.events.wb_round_overflow <= wb_round_overflow;
            fp_tr.events.roundup <= roundup;
            fp_tr.sigs.in_flight_ids <= in_flight_ids;
        end
        //operand_stall_source_check:
            //assert property (@(posedge clk) disable iff (rst)
                //fp_operand_stall |-> $onehot({operand_stall_due_to_fls, operand_stall_due_to_fmadd, operand_stall_due_to_fdiv_sqrt, operand_stall_due_to_wb2fp, 1'b0})
                //);
    end endgenerate

    ////////////////////////////////////////////////////
    //Assertion Binding
endmodule
