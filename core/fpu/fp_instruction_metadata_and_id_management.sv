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

module fp_instruction_metadata_and_id_management

    import taiga_config::*;
    import taiga_types::*;
    import fpu_types::*;

    (
        input logic clk,
        input logic rst,
        input id_t fetch_id,
        input fetch_complete,
        input logic [31:0] fetch_instruction,

        input retire_packet_t retire,

        input id_t decode_id,
        output decode_wb2_float,
        output decode_is_float,
        output decode_accu_fcsr,
        output decode_wb2_int,
        output decode_need_int,

        input issue_packet_t issue,
        input logic instruction_issued,

        input id_t retire_ids_next [RETIRE_PORTS],
        output logic [RETIRE_PORTS-1:0] retire_is_float, 
        output logic [RETIRE_PORTS-1:0] retire_is_accu_fcsr,
        output logic [RETIRE_PORTS-1:0] retire_is_wb2_float,

        input phys_addr_t phys_addr_table [MAX_IDS],
        input fp_wb_packet_t fp_wb_packet [FP_NUM_WB_GROUPS],
        output fp_commit_packet_t fp_commit_packet [FP_NUM_WB_GROUPS],

        output fcsr_fifo_data_t oldest_fp_issued_fifo_data_out,
        output logic oldest_fp_issued_fifo_pop 
    );

    (* ramstyle = "MLAB, no_rw_check" *) logic [0:0] is_float_table [MAX_IDS];
    (* ramstyle = "MLAB, no_rw_check" *) logic [0:0] wb2_float_table [MAX_IDS];
    (* ramstyle = "MLAB, no_rw_check" *) logic [0:0] accu_fcsr_table [MAX_IDS];
    (* ramstyle = "MLAB, no_rw_check" *) logic [0:0] wb2_int_table [MAX_IDS];
    (* ramstyle = "MLAB, no_rw_check" *) logic [0:0] need_int_data_table [MAX_IDS];

    //////////////////////////////////////////
    //Implementation

    //////////////////////////////////////////
    //Instruction Attribute Tables
    logic fetch_need_int_data;
    logic fetch_wb2_int;
    logic fetch_need_float_data;
    logic fetch_wb2_float;
    logic fetch_is_float;
    logic fetch_accu_fcsr;

    fp_illegal_instruction_checker fp_inst_attr(
        .instruction (fetch_instruction),
        .need_int_data (fetch_need_int_data),
        .write_int_data (fetch_wb2_int),
        .need_float_data (fetch_need_float_data),
        .write_float_data (fetch_wb2_float),
        .float_instruction (fetch_is_float),
        .accumulating_csrs (fetch_accu_fcsr)
    );

    //////////////////////////////////////////
    //Decode Instruction Attributes
    always_ff @ (posedge clk) begin
        if (fetch_complete) begin
            accu_fcsr_table[fetch_id] <= fetch_accu_fcsr;
            wb2_float_table[fetch_id] <= fetch_wb2_float;
            is_float_table[fetch_id] <= fetch_is_float;
            wb2_int_table[fetch_id] <= fetch_wb2_int;
            need_int_data_table[fetch_id] <= fetch_need_int_data;
        end
    end

    assign decode_accu_fcsr = accu_fcsr_table[decode_id];
    assign decode_wb2_float = wb2_float_table[decode_id];
    assign decode_is_float  = is_float_table[decode_id];
    assign decode_wb2_int = wb2_int_table[decode_id];
    assign decode_need_int = need_int_data_table[decode_id];

    //////////////////////////////////////////
    //FCSR support
    fifo_interface #($bits(fcsr_fifo_data_t)) oldest_fp_issued_fifo(); 
    taiga_fifo #(.DATA_WIDTH($bits(fcsr_fifo_data_t)), .FIFO_DEPTH(MAX_IDS))
        fp_issued_id_fifo (
            .clk (clk),
            .rst (rst),
            .fifo (oldest_fp_issued_fifo)
        );

    assign oldest_fp_issued_fifo.data_in = {issue.id, issue.wb2_float}; 
    assign oldest_fp_issued_fifo.potential_push = instruction_issued & issue.accumulating_csrs;
    assign oldest_fp_issued_fifo.push = oldest_fp_issued_fifo.potential_push;
    assign oldest_fp_issued_fifo.pop = retire.accumulating_csrs;
    assign oldest_fp_issued_fifo_data_out = oldest_fp_issued_fifo.data_out;
    assign oldest_fp_issued_fifo_pop = oldest_fp_issued_fifo.pop;

    //////////////////////////////////////////
    //Retirer
    genvar i;
    generate for (i = 0; i < RETIRE_PORTS; i++) begin
        assign retire_is_float[i] = wb2_float_table[retire_ids_next[i]];
        assign retire_is_wb2_float[i] = wb2_float_table[retire_ids_next[i]];
        assign retire_is_accu_fcsr[i] = accu_fcsr_table[retire_ids_next[i]];
    end endgenerate

    //////////////////////////////////////////
    //Writeback/Commit support
    phys_addr_t commit_phys_addr [FP_NUM_WB_GROUPS];
    generate for (i = 0; i < FP_NUM_WB_GROUPS; i++) begin
        assign commit_phys_addr[i] = phys_addr_table[fp_wb_packet[i].id];
    end endgenerate

    generate for (i = 0; i < FP_NUM_WB_GROUPS; i++) begin
        assign fp_commit_packet[i].id = fp_wb_packet[i].id;
        assign fp_commit_packet[i].phys_addr = commit_phys_addr[i];        
        assign fp_commit_packet[i].valid = fp_wb_packet[i].valid;

        //MCA Only
        sandbox #(.SANDBOX_FRAC_W(FRAC_WIDTH), .SANDBOX_EXPO_W(EXPO_WIDTH))
        sandbox_inst (
            .data_in (fp_wb_packet[i].data),
            .data_out (fp_commit_packet[i].data)
        );
    end endgenerate
endmodule 
