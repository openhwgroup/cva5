/*
 * Copyright © 2020 Eric Matthews,  Lesley Shannon
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

module renamer

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

        //Decode
        input logic decode_advance,
        renamer_interface.renamer decode,

        //Issue stage
        input issue_packet_t issue,
        input logic instruction_issued_with_rd,

        //Retire response
        input retire_packet_t retire
    );
    //////////////////////////////////////////
    typedef struct packed{
        rs_addr_t rd_addr;
        phys_addr_t spec_phys_addr;
        phys_addr_t previous_phys_addr;
        logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] previous_wb_group;
    } renamer_metadata_t;
    renamer_metadata_t inuse_list_input;
    renamer_metadata_t inuse_list_output;

    logic [5:0] clear_index;

    fifo_interface #(.DATA_WIDTH($bits(phys_addr_t))) free_list ();
    fifo_interface #(.DATA_WIDTH($bits(renamer_metadata_t))) inuse_list ();

    logic rename_valid;
    logic rollback;
    ////////////////////////////////////////////////////
    //Implementation
    //Assumption: MAX_IDS <= 32 thus, decode/rename stage can never stall due to lacking a free register
    //Zero register is never renamed
    //If a renamed destination is flushed in the issue stage, state is rolled back
    //When an instruction reaches the retire stage it either commits or reverts its renaming depending on whether the instruction retires or is discarded
    assign rename_valid = (~gc.fetch_flush) & decode_advance & decode.uses_rd & |decode.rd_addr;

    //Revert physcial address assignment on a flush
    assign rollback = gc.fetch_flush & issue.stage_valid & issue.uses_rd & |issue.rd_addr;

    //counter for indexing through memories for post-reset clearing/initialization
    lfsr #(.WIDTH(6), .NEEDS_RESET(0))
    lfsr_read_index (
        .clk (clk), .rst (rst),
        .en(gc.init_clear),
        .value(clear_index)
    );

    ////////////////////////////////////////////////////
    //Free list FIFO
    register_free_list #(.DATA_WIDTH($bits(phys_addr_t)), .FIFO_DEPTH(32)) free_list_fifo (
        .clk (clk),
        .rst (rst),
        .fifo (free_list),
        .rollback (rollback)
    );

    //During post reset init, initialize FIFO with free list (registers 32-63)
    assign free_list.potential_push = (gc.init_clear & ~clear_index[5]) | (retire.valid);
    assign free_list.push = free_list.potential_push;

    assign free_list.data_in = gc.init_clear ? {1'b1, clear_index[4:0]} : (gc.writeback_supress ? inuse_list_output.spec_phys_addr : inuse_list_output.previous_phys_addr);
    assign free_list.pop = rename_valid;

    ////////////////////////////////////////////////////
    //Inuse list FIFO
    cva5_fifo #(.DATA_WIDTH($bits(renamer_metadata_t)), .FIFO_DEPTH(32)) inuse_list_fifo (
        .clk (clk),
        .rst (rst),
        .fifo (inuse_list)
    );

    assign inuse_list.potential_push = instruction_issued_with_rd & |issue.rd_addr;
    assign inuse_list.push = inuse_list.potential_push;

    assign inuse_list_input.rd_addr = issue.rd_addr;
    assign inuse_list_input.spec_phys_addr = issue.phys_rd_addr;
    assign inuse_list_input.previous_phys_addr = spec_table_previous_r.phys_addr;
    assign inuse_list_input.previous_wb_group = spec_table_previous_r.wb_group;
    assign inuse_list.data_in = inuse_list_input;

    assign inuse_list_output = inuse_list.data_out;
    assign inuse_list.pop = retire.valid;

    ////////////////////////////////////////////////////
    //Speculative rd-to-phys Table
    //On rollback restore the previous contents
    //During post reset init, initialize rd_to_phys with in-use list (lower 32 registers)
    typedef struct packed{
        phys_addr_t phys_addr;
        logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] wb_group;
    } spec_table_t;
    rs_addr_t spec_table_read_addr [REGFILE_READ_PORTS+1];
    spec_table_t spec_table_read_data [REGFILE_READ_PORTS+1];

    spec_table_t spec_table_next;
    spec_table_t spec_table_next_mux [4];
    spec_table_t spec_table_previous;
    spec_table_t spec_table_previous_r;

    logic spec_table_update;
    rs_addr_t spec_table_write_index;
    rs_addr_t spec_table_write_index_mux [4];

    assign spec_table_update =  rename_valid | rollback | gc.init_clear | (retire.valid & gc.writeback_supress);

    logic [1:0] spec_table_sel;
    
    one_hot_to_integer #(.C_WIDTH(4)) spec_table_sel_one_hot_to_int (
        .one_hot ({gc.init_clear, rollback, (retire.valid & gc.writeback_supress), 1'b0}),
        .int_out (spec_table_sel)
    );

    //Normal operation
    assign spec_table_write_index_mux[0] = decode.rd_addr;
    assign spec_table_next_mux[0].phys_addr = free_list.data_out;
    assign spec_table_next_mux[0].wb_group = decode.rd_wb_group;
    //gc.writeback_supress
    assign spec_table_write_index_mux[1] = inuse_list_output.rd_addr;
    assign spec_table_next_mux[1].phys_addr = inuse_list_output.previous_phys_addr;
    assign spec_table_next_mux[1].wb_group = inuse_list_output.previous_wb_group;
    //rollback
    assign spec_table_write_index_mux[2] = issue.rd_addr;
    assign spec_table_next_mux[2].phys_addr = spec_table_previous_r.phys_addr;
    assign spec_table_next_mux[2].wb_group = spec_table_previous_r.wb_group;
    //gc.init_clear
    assign spec_table_write_index_mux[3] = clear_index[4:0];
    assign spec_table_next_mux[3].phys_addr = {1'b0, clear_index[4:0]};
    assign spec_table_next_mux[3].wb_group = '0;

    assign spec_table_write_index = spec_table_write_index_mux[spec_table_sel];
    assign spec_table_next = spec_table_next_mux[spec_table_sel];

    assign spec_table_read_addr[0] = spec_table_write_index;
    assign spec_table_read_addr[1:REGFILE_READ_PORTS] = '{decode.rs_addr[RS1], decode.rs_addr[RS2]};

    lutram_1w_mr #(
        .WIDTH($bits(spec_table_t)),
        .DEPTH(32),
        .NUM_READ_PORTS(REGFILE_READ_PORTS+1)
    )
    spec_table_ram (
        .clk(clk),
        .waddr(spec_table_write_index),
        .raddr(spec_table_read_addr),
        .ram_write(spec_table_update),
        .new_ram_data(spec_table_next),
        .ram_data_out(spec_table_read_data)
    );
    assign spec_table_previous = spec_table_read_data[0];

    always_ff @ (posedge clk) begin
        if (spec_table_update) begin
            spec_table_previous_r <= spec_table_previous;
        end
    end

    ////////////////////////////////////////////////////
    //Renamed Outputs
    spec_table_t [REGFILE_READ_PORTS-1:0] spec_table_decode;
    generate for (genvar i = 0; i < REGFILE_READ_PORTS; i++) begin : gen_renamed_addrs
        assign spec_table_decode[i] = spec_table_read_data[i+1];
        assign decode.phys_rs_addr[i] = spec_table_decode[i].phys_addr;
        assign decode.rs_wb_group[i] = spec_table_decode[i].wb_group;
    end endgenerate

    assign decode.phys_rd_addr = |decode.rd_addr ? free_list.data_out : '0;
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    rename_rd_zero_assertion:
        assert property (@(posedge clk) disable iff (rst) (decode.rd_addr == 0) |-> (decode.phys_rd_addr == 0)) else $error("rd zero renamed");

    for (genvar i = 0; i < REGFILE_READ_PORTS; i++) begin : rename_rs_zero_assertion
        assert property (@(posedge clk) disable iff (rst) (decode.rs_addr[i] == 0) |-> (decode.phys_rs_addr[i] == 0)) else $error("rs zero renamed");
    end

endmodule
