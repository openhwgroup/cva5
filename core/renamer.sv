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

    import taiga_config::*;
    import taiga_types::*;

    (
        input logic clk,
        input logic rst,

        input logic gc_init_clear,
        input logic gc_fetch_flush,

        //Decode
        input logic decode_advance,
        renamer_interface.renamer decode,

        //Issue stage
        input issue_packet_t issue,

        //Retire response
        input retire_packet_t retire
    );
    //////////////////////////////////////////
    phys_addr_t architectural_id_to_phys_table [MAX_IDS];
    phys_addr_t speculative_rd_to_phys_table [32];

    rs_wb_group_t spec_wb_group [32];
    rs_wb_group_t arch_wb_group [32];
    rs_wb_group_t rollback_wb_group;

    logic [5:0] clear_index;
    fifo_interface #(.DATA_WIDTH(6)) free_list ();
    logic rename_valid;
    logic rollback;
    phys_addr_t rollback_phys_addr;
    ////////////////////////////////////////////////////
    //Implementation
    assign rename_valid = (~gc_fetch_flush) & decode_advance & decode.uses_rd & |decode.rd_addr;

    //Revert physcial address assignment on a flush
    assign rollback = gc_fetch_flush & issue.stage_valid & issue.uses_rd & |issue.rd_addr;

    //counter for indexing through memories for post-reset clearing/initialization
    initial clear_index = 0;
    always_ff @ (posedge clk) begin
        if (rst)
            clear_index <= 0;
        else
            clear_index <= clear_index + 6'(gc_init_clear);
    end
    ////////////////////////////////////////////////////
    //Free list FIFO
    register_free_list #(.DATA_WIDTH(6), .FIFO_DEPTH(32)) free_list_fifo (
        .clk (clk),
        .rst (rst),
        .fifo (free_list),
        .rollback (rollback)
    );

    //During post reset init, initialize FIFO with free list (registers 32-63)
    assign free_list.potential_push = (gc_init_clear & ~clear_index[5]) | (retire.valid);
    assign free_list.push = free_list.potential_push;
    //TODO: restore spec if instruction has been discarded due to a speculation failure
    assign free_list.data_in = gc_init_clear ? {1'b1, clear_index[4:0]} : architectural_id_to_phys_table[retire.phys_id];
    assign free_list.pop = rename_valid;

    ////////////////////////////////////////////////////
    //Speculative rd-to-phys Table
    //On rollback restore the previous contents
    //During post reset init, initialize rd_to_phys with in-use list (lower 32 registers)
    logic spec_table_update;
    logic [4:0] spec_table_write_index;
    logic [5:0] spec_table_write_data;
    logic [$clog2(NUM_WB_GROUPS)-1:0] spec_table_wb_group_data;

    assign spec_table_update =  rename_valid | rollback | gc_init_clear;

    always_comb begin
        if (gc_init_clear) begin
            spec_table_write_index = clear_index[4:0];
            spec_table_write_data = {1'b0, clear_index[4:0]};
            spec_table_wb_group_data = '0;
        end
        else if (rollback) begin
            spec_table_write_index = issue.rd_addr;
            spec_table_write_data = rollback_phys_addr;
            spec_table_wb_group_data = rollback_wb_group;
        end
        else begin
            spec_table_write_index = decode.rd_addr;
            spec_table_write_data = free_list.data_out;
            spec_table_wb_group_data = decode.rd_wb_group;
        end
    end

    always_ff @ (posedge clk) begin
        if (spec_table_update) begin
            speculative_rd_to_phys_table[spec_table_write_index] <= spec_table_write_data;
            rollback_phys_addr <= speculative_rd_to_phys_table[spec_table_write_index];
        end
    end
    
    //WB group
    always_ff @ (posedge clk) begin
        if (spec_table_update) begin
            spec_wb_group[spec_table_write_index] <= spec_table_wb_group_data;
            rollback_wb_group <= spec_wb_group[spec_table_write_index];
        end
    end

    ////////////////////////////////////////////////////
    //Arch ID-to-phys Table
    always_ff @ (posedge clk) begin
        if (rename_valid)
            architectural_id_to_phys_table[decode.id] <= speculative_rd_to_phys_table[spec_table_write_index];
    end

    ////////////////////////////////////////////////////
    //Renamed Outputs
    always_comb begin
        for (int i = 0; i < REGFILE_READ_PORTS; i++) begin
            decode.phys_rs_addr[i] = speculative_rd_to_phys_table[decode.rs_addr[i]];
            decode.rs_wb_group[i] = spec_wb_group[decode.rs_addr[i]];
        end
    end

    assign decode.phys_rd_addr = rename_valid ? free_list.data_out : '0;
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
