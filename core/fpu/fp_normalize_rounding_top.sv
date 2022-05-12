/*
 * Copyright © 2017, 2018, 2019 Eric Matthews,  Lesley Shannon
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
 *                  Yuhui Gao <yuhuig@sfu.ca>
 */

import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module fp_normalize_rounding_top #(
        parameter int unsigned NUM_WB_UNITS = 3,
        parameter int unsigned NUM_UNITS [FP_NUM_WB_GROUPS] = '{3}
    )
    (
        input logic clk,
        input logic rst,
        fp_unit_writeback_interface.wb intermediate_unit_wb[NUM_WB_UNITS],
        fp_unit_writeback_interface.unit unit_wb
    );

    //Writeback
    //aliases for write-back-interface signals
    logic [NUM_WB_UNITS-1:0] unit_ack [FP_NUM_WB_GROUPS];
    id_t [NUM_WB_UNITS-1:0] unit_instruction_id [FP_NUM_WB_GROUPS];

    logic [NUM_WB_UNITS-1:0] unit_done [FP_NUM_WB_GROUPS];

    typedef logic [FLEN-1:0] unit_rd_t [NUM_WB_UNITS];
    unit_rd_t unit_rd [FP_NUM_WB_GROUPS];

    logic [NUM_WB_UNITS-1:0] unit_carry [FP_NUM_WB_GROUPS];
    logic [NUM_WB_UNITS-1:0] unit_safe [FP_NUM_WB_GROUPS];
    logic [NUM_WB_UNITS-1:0] unit_hidden [FP_NUM_WB_GROUPS];
    logic [NUM_WB_UNITS-1:0] unit_expo_overflow [FP_NUM_WB_GROUPS];
    logic [NUM_WB_UNITS-1:0] unit_right_shift [FP_NUM_WB_GROUPS];
    logic [NUM_WB_UNITS-1:0] unit_subnormal [FP_NUM_WB_GROUPS];

    typedef logic [2:0] unit_rm_t;
    unit_rm_t [NUM_WB_UNITS-1:0] unit_rm [FP_NUM_WB_GROUPS];

    typedef logic [4:0] unit_fflags_t [NUM_WB_UNITS];
    unit_fflags_t unit_fflags [FP_NUM_WB_GROUPS];

    fp_shift_amt_t [NUM_WB_UNITS-1:0] unit_clz [FP_NUM_WB_GROUPS];

    grs_t [NUM_WB_UNITS-1:0] unit_grs [FP_NUM_WB_GROUPS];

    typedef logic [EXPO_WIDTH-1:0] unit_right_shift_amt_t;
    unit_right_shift_amt_t [NUM_WB_UNITS-1:0] unit_right_shift_amt [FP_NUM_WB_GROUPS];

    //Per-ID muxes for commit buffer
    logic [$clog2(NUM_WB_UNITS)-1:0] unit_sel [FP_NUM_WB_GROUPS];

    //Shared normalization
    fp_normalize_packet_t normalize_packet, normalize_packet_r;

    //Shared rounding
    fp_round_packet_t round_packet, round_packet_r;

    typedef int unsigned unit_count_t [FP_NUM_WB_GROUPS];
    function unit_count_t get_cumulative_unit_count();
    unit_count_t counts;
    int unsigned cumulative_count = 0;
    for (int i = 0; i < FP_NUM_WB_GROUPS; i++) begin
        counts[i] = cumulative_count;
        cumulative_count += NUM_UNITS[i];
    end
    return counts;
    endfunction
    
    localparam unit_count_t CUMULATIVE_NUM_UNITS = get_cumulative_unit_count();
  
    genvar i, j, k;
    ////////////////////////////////////////////////////
    //Implementation
    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    generate
        for (i = 0; i < FP_NUM_WB_GROUPS; i++) begin
            for (j = 0; j < NUM_UNITS[i]; j++) begin
                assign unit_instruction_id[i][j] = intermediate_unit_wb[CUMULATIVE_NUM_UNITS[i] + j].id;
                assign unit_done[i][j] = intermediate_unit_wb[CUMULATIVE_NUM_UNITS[i] + j].done;
                assign unit_rm[i][j] = intermediate_unit_wb[CUMULATIVE_NUM_UNITS[i] + j].rm;
                assign unit_grs[i][j] = intermediate_unit_wb[CUMULATIVE_NUM_UNITS[i] + j].grs;
                assign unit_carry[i][j] = intermediate_unit_wb[CUMULATIVE_NUM_UNITS[i] + j].carry;
                assign unit_safe[i][j] = intermediate_unit_wb[CUMULATIVE_NUM_UNITS[i] + j].safe;
                assign unit_hidden[i][j] = intermediate_unit_wb[CUMULATIVE_NUM_UNITS[i] + j].hidden;
                assign unit_clz[i][j] = intermediate_unit_wb[CUMULATIVE_NUM_UNITS[i] + j].clz;
                assign unit_subnormal[i][j] = intermediate_unit_wb[CUMULATIVE_NUM_UNITS[i] + j].subnormal;
                assign unit_right_shift[i][j] = intermediate_unit_wb[CUMULATIVE_NUM_UNITS[i] + j].right_shift;
                assign unit_right_shift_amt[i][j] = intermediate_unit_wb[CUMULATIVE_NUM_UNITS[i] + j].right_shift_amt;
                assign intermediate_unit_wb[CUMULATIVE_NUM_UNITS[i] + j].ack = unit_ack[i][j];
            end
        end
    endgenerate

    //As units are selected for commit ports based on their unit ID,
    //for each additional commit port one unit can be skipped for the commit mux
    generate
        for (i = 0; i < FP_NUM_WB_GROUPS; i++) begin
            for (j = 0; j < NUM_UNITS[i]; j++) begin
                assign unit_rd[i][j] = intermediate_unit_wb[CUMULATIVE_NUM_UNITS[i] + j].rd;
                assign unit_expo_overflow[i][j] = intermediate_unit_wb[CUMULATIVE_NUM_UNITS[i] + j].expo_overflow;
                assign unit_fflags[i][j] = intermediate_unit_wb[CUMULATIVE_NUM_UNITS[i] + j].fflags;
            end
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Unit select for normalization module
    generate for (i = 0; i < FP_NUM_WB_GROUPS; i++) begin
        priority_encoder
            #(.WIDTH(NUM_UNITS[i]))
        unit_done_encoder
        (
            .priority_vector (unit_done[i][NUM_UNITS[i]-1 : 0]),
            .encoded_result (unit_sel[i][NUM_UNITS[i] == 1 ? 0 : ($clog2(NUM_UNITS[i])-1) : 0])
        );
    end endgenerate

    always_comb begin
        for (int i = 0; i < FP_NUM_WB_GROUPS; i++) begin
            //ID, data and rounding signals muxes
            normalize_packet.valid = |unit_done[i];
            normalize_packet.id = unit_instruction_id[i][unit_sel[i]];
            normalize_packet.data = unit_rd[i][unit_sel[i]];
            normalize_packet.expo_overflow = unit_expo_overflow[i][unit_sel[i]];
            normalize_packet.fflags =  unit_fflags[i][unit_sel[i]];
            normalize_packet.rm =  unit_rm[i][unit_sel[i]];
            normalize_packet.carry = unit_carry[i][unit_sel[i]];
            normalize_packet.safe = unit_safe[i][unit_sel[i]];
            normalize_packet.hidden = unit_hidden[i][unit_sel[i]];
            normalize_packet.grs = unit_grs[i][unit_sel[i]];
            normalize_packet.clz = unit_clz[i][unit_sel[i]];
            normalize_packet.subnormal = unit_subnormal[i][unit_sel[i]];
            normalize_packet.right_shift = unit_right_shift[i][unit_sel[i]];
            normalize_packet.right_shift_amt = unit_right_shift_amt[i][unit_sel[i]];
            //Unit Ack
            unit_ack[i] = '0;
            unit_ack[i][unit_sel[i]] = advance_norm & normalize_packet.valid; //writeback not valid until the normalization stage is ready
        end    
    end

    ////////////////////////////////////////////////////
    //Shared normalzation
    logic result_sign, result_sign_norm;
    logic [EXPO_WIDTH-1:0] result_expo, result_expo_norm;
    logic expo_overflow, expo_overflow_norm;
    logic [FRAC_WIDTH-1:0] result_frac, result_frac_norm;
    logic subnormal;
    logic right_shift;
    logic [EXPO_WIDTH-1:0] right_shift_amt;
    fp_shift_amt_t clz;
    logic carry;
    logic safe;
    logic hidden, hidden_norm;
    grs_t grs, grs_norm;
    logic overflow_before_rounding;
    logic roundup;
    logic [FLEN-1:0]             result_if_overflow;
    logic advance_norm;

    //TODO: add clock enable 
    always_ff @ (posedge clk) begin
        if (advance_norm)
            normalize_packet_r <= normalize_packet;
    end
    
    //unpack
    assign result_sign = normalize_packet_r.data[FLEN-1];
    assign expo_overflow = normalize_packet_r.expo_overflow;
    assign result_expo = normalize_packet_r.data[FLEN-2-:EXPO_WIDTH];
    assign result_frac = normalize_packet_r.data[FRAC_WIDTH-1:0];
    assign clz = normalize_packet_r.clz;
    assign carry = normalize_packet_r.carry;
    assign safe = normalize_packet_r.safe;
    assign hidden = normalize_packet_r.hidden;
    assign grs = normalize_packet_r.grs;
    assign subnormal = normalize_packet_r.subnormal;
    assign right_shift = normalize_packet_r.right_shift;
    assign right_shift_amt = normalize_packet_r.right_shift_amt;

    //normalization
    fp_normalize normalize_inst(
      .sign(result_sign),
      .expo(result_expo),
      .expo_overflow(expo_overflow),
      .frac(result_frac),
      .left_shift_amt(clz),
      .subnormal(subnormal),
      .right_shift(right_shift),
      .right_shift_amt(right_shift_amt),
      .hidden_bit(hidden),
      .frac_safe_bit(safe),
      .frac_carry_bit(carry),
      .grs_in(grs),
      .sign_norm(result_sign_norm),
      .expo_norm(result_expo_norm),
      .expo_overflow_norm(expo_overflow_norm),
      .frac_norm(result_frac_norm),
      .hidden_bit_norm(hidden_norm),
      .grs_norm(grs_norm),
      .overflow_before_rounding(overflow_before_rounding)
    );

    //roundup calculation
    fp_round_simplified round(
      .sign(result_sign_norm),
      .rm(normalize_packet_r.rm),
      .grs({grs_norm[GRS_WIDTH-1-:2], |grs_norm[0+:GRS_WIDTH-2]}), 
      .lsb(result_frac_norm[0]),
      .roundup(round_packet.roundup),
      .result_if_overflow(result_if_overflow)
    );

    //prep for rounding 
    assign round_packet.valid = normalize_packet_r.valid;
    assign round_packet.data = {result_sign_norm, result_expo_norm, result_frac_norm};
    assign round_packet.expo_overflow = expo_overflow_norm;
    assign round_packet.hidden = hidden_norm;
    assign round_packet.id = normalize_packet_r.id;
    assign round_packet.valid = normalize_packet_r.valid;
    assign round_packet.result_if_overflow = result_if_overflow;
    assign round_packet.fflags = {normalize_packet_r.fflags[4:1], normalize_packet_r.fflags[0] | |grs_norm};
    assign round_packet.overflow_before_rounding = overflow_before_rounding;

    ////////////////////////////////////////////////////
    //Shared rounding 
    logic [FRAC_WIDTH:0]         frac_round_intermediate;
    logic                        frac_overflow, frac_overflow_placeholder;
    logic                        sign_out;
    logic [EXPO_WIDTH-1:0]       expo, expo_out;
    logic                        expo_overflow_round;
    logic [FRAC_WIDTH-1:0]       frac, frac_out;
    logic                        hidden_round;
    logic [4:0]                  fflags, fflags_out;
    logic                        wb_valid;
    logic                        overflowExp, overflowExp_intermediate, underflowExp;
    logic frac_overflow_debug;
    logic advance_round;

    //TODO: add clock enable 
    always_ff @ (posedge clk) begin
        if (advance_round)
            round_packet_r <= round_packet;
    end

    assign frac_overflow = &{hidden_round, frac, roundup};
    assert property (@(posedge clk) (frac_overflow|frac_overflow_debug) -> (frac_overflow_debug == frac_overflow));

    assign wb_valid = round_packet_r.valid;
    assign roundup = round_packet_r.roundup;
    assign sign_out = round_packet_r.data[FLEN-1];
    assign expo = round_packet_r.data[FLEN-2-:EXPO_WIDTH];
    assign expo_overflow_round = round_packet_r.expo_overflow;
    assign frac = round_packet_r.data[FRAC_WIDTH-1:0];
    assign hidden_round = round_packet_r.hidden;
    assign fflags = round_packet_r.fflags;
    // frac_overflow can be calculated in parallel with roundup
    assign {frac_overflow_debug, frac_round_intermediate} = {hidden_round, frac} + (FRAC_WIDTH+2)'(roundup);
    assign frac_out = frac_round_intermediate[FRAC_WIDTH-1:0] >> frac_overflow;
    assign {overflowExp_intermediate, expo_out} = {expo_overflow_round, expo} + EXPO_WIDTH'(frac_overflow); 
    assign overflowExp = overflowExp_intermediate | round_packet_r.overflow_before_rounding;
    assign underflowExp = ~(hidden_round) & |frac_out;
    assign fflags_out = fflags[4] ? fflags : fflags | {2'b0, overflowExp, underflowExp, overflowExp}; //inexact is asserted when overflow 

    //Pipeline Control
    //The dummy writeback cannot advance unless the actual writeback stage allows, or either norm/round stage not valid
    assign advance_round = unit_wb.ack | ~round_packet_r.valid;
    assign advance_norm = advance_round | ~normalize_packet_r.valid;

    //Output
    assign unit_wb.id = round_packet_r.id;
    assign unit_wb.done = round_packet_r.valid;
    assign unit_wb.rd = overflowExp ? round_packet_r.result_if_overflow : {sign_out, expo_out, frac_out};
    assign unit_wb.fflags = fflags_out;

endmodule
