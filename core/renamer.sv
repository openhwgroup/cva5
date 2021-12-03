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

        //Retire response
        input retire_packet_t retire
    );
    //////////////////////////////////////////
    (* ramstyle = "MLAB, no_rw_check" *) phys_addr_t architectural_id_to_phys_table [MAX_IDS];

    logic [5:0] clear_index;
    fifo_interface #(.DATA_WIDTH(6)) free_list ();
    logic rename_valid;
    logic rollback;
    ////////////////////////////////////////////////////
    //Implementation
    assign rename_valid = (~gc.fetch_flush) & decode_advance & decode.uses_rd & |decode.rd_addr;

    //Revert physcial address assignment on a flush
    assign rollback = gc.fetch_flush & issue.stage_valid & issue.uses_rd & |issue.rd_addr;

    //counter for indexing through memories for post-reset clearing/initialization
    initial clear_index = 0;
    always_ff @ (posedge clk) begin
        if (rst)
            clear_index <= 0;
        else
            clear_index <= clear_index + 6'(gc.init_clear);
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
    assign free_list.potential_push = (gc.init_clear & ~clear_index[5]) | (retire.valid & ~retire.wb2_float);
    assign free_list.push = free_list.potential_push;
    //TODO: restore spec if instruction has been discarded due to a speculation failure
    assign free_list.data_in = gc.init_clear ? {1'b1, clear_index[4:0]} : architectural_id_to_phys_table[retire.phys_id];
    assign free_list.pop = rename_valid;

    ////////////////////////////////////////////////////
    //Speculative rd-to-phys Table
    //On rollback restore the previous contents
    //During post reset init, initialize rd_to_phys with in-use list (lower 32 registers)
    typedef struct packed{
        phys_addr_t phys_addr;
        logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] wb_group;
    } spec_table_t;
    logic [4:0] spec_table_read_addr [REGFILE_READ_PORTS+1];
    spec_table_t spec_table_read_data [REGFILE_READ_PORTS+1];

    spec_table_t spec_table_next;
    spec_table_t spec_table_old;
    spec_table_t spec_table_old_r;

    logic spec_table_update;
    logic [4:0] spec_table_write_index;

    assign spec_table_update =  rename_valid | rollback | gc.init_clear;

    always_comb begin
        if (gc.init_clear) begin
            spec_table_write_index = clear_index[4:0];
            spec_table_next.phys_addr = {1'b0, clear_index[4:0]};
            spec_table_next.wb_group = '0;
        end
        else if (rollback) begin
            spec_table_write_index = issue.rd_addr;
            spec_table_next.phys_addr = spec_table_old_r.phys_addr;
            spec_table_next.wb_group = spec_table_old_r.wb_group;
        end
        else begin
            spec_table_write_index = decode.rd_addr;
            spec_table_next.phys_addr = free_list.data_out;
            spec_table_next.wb_group = decode.rd_wb_group;
        end
    end

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
    assign spec_table_old = spec_table_read_data[0];

    always_ff @ (posedge clk) begin
        if (spec_table_update) begin
            spec_table_old_r <= spec_table_old;
        end
    end

    ////////////////////////////////////////////////////
    //Arch ID-to-phys Table
    always_ff @ (posedge clk) begin
        if (rename_valid)
            architectural_id_to_phys_table[decode.id] <= spec_table_old.phys_addr;
    end

    ////////////////////////////////////////////////////
    //Renamed Outputs
    spec_table_t [REGFILE_READ_PORTS-1:0] spec_table_decode;
    generate for (genvar i = 0; i < REGFILE_READ_PORTS; i++) begin
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
