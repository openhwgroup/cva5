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
    logic [FLEN-1:0]             result_if_overflow;
    logic advance_norm;
    fp_normalize_pre_processing_packet_t normalize_pre_processing_packet;

    assign advance_norm = advance_shift | ~normalize_packet_r.valid;
    always_ff @ (posedge clk) begin
        if (advance_norm)
            normalize_packet_r <= normalize_packet;
    end
    
    //normalization
    fp_normalize normalize_inst(
      .fp_normalize_packet(normalize_packet_r),
      .fp_normalize_pre_processing_packet(normalize_pre_processing_packet)
    );

    ////////////////////////////////////////////////////
    //Shifter
    logic advance_shift;
    fp_normalize_pre_processing_packet_t normalize_pre_processing_packet_r;
    logic [EXPO_WIDTH-1:0] shift_amt;
    logic right_shift;
    logic signed [FRAC_WIDTH+3+GRS_WIDTH-1:0] shifter_in, result, result_reversed;
    logic                  result_sign_norm;
    logic [EXPO_WIDTH-1:0] result_expo_norm;
    logic expo_overflow_norm;
    logic [FRAC_WIDTH-1:0] result_frac_norm;
    logic overflow_before_rounding;
    logic carry_norm;
    logic safe_norm;
    logic hidden_norm;
    grs_t grs_norm;

    always_comb begin
        right_shift = normalize_pre_processing_packet_r.right_shift;
        shift_amt = normalize_pre_processing_packet_r.shift_amt;
        shifter_in = normalize_pre_processing_packet_r.shifter_in;
        result = shifter_in >>> shift_amt;
        result_reversed = reverse(result);

        {carry_norm, safe_norm, hidden_norm, result_frac_norm, grs_norm} = right_shift ? result : result_reversed;
        result_sign_norm = normalize_pre_processing_packet_r.sign_norm;
        result_expo_norm = normalize_pre_processing_packet_r.expo_norm;
        expo_overflow_norm = normalize_pre_processing_packet_r.expo_overflow_norm;
        overflow_before_rounding = normalize_pre_processing_packet_r.overflow_before_rounding;
    end

    assign advance_shift = advance_round | ~normalize_pre_processing_packet_r.valid;
    always_ff @ (posedge clk) begin
        if (advance_shift) 
            normalize_pre_processing_packet_r <= normalize_pre_processing_packet;
    end

    //roundup calculation
    fp_round_simplified round(
      .sign(result_sign_norm),
      .rm(normalize_pre_processing_packet_r.rm),
      .grs({grs_norm[GRS_WIDTH-1-:2], |grs_norm[0+:GRS_WIDTH-2]}), 
      .lsb(result_frac_norm[0]),
      .roundup(round_packet.roundup),
      .result_if_overflow(result_if_overflow)
    );

    //prep for rounding 
    assign round_packet.valid = normalize_pre_processing_packet_r.valid;
    assign round_packet.data = {result_sign_norm, result_expo_norm, result_frac_norm};
    assign round_packet.expo_overflow = expo_overflow_norm;
    assign round_packet.hidden = hidden_norm;
    assign round_packet.id = normalize_pre_processing_packet_r.id;
    assign round_packet.valid = normalize_pre_processing_packet_r.valid;
    assign round_packet.result_if_overflow = result_if_overflow;
    assign round_packet.fflags = {normalize_pre_processing_packet_r.fflags[4:1], normalize_pre_processing_packet_r.fflags[0] | |grs_norm};
    assign round_packet.overflow_before_rounding = overflow_before_rounding;

    ////////////////////////////////////////////////////
    //Shared rounding 
    logic [FRAC_WIDTH+1:0]       hidden_round_frac_roundup;
    logic [FRAC_WIDTH:0]         frac_round_intermediate;
    logic                        roundup;
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

    localparam NUM_FRAC_LUTS = (FRAC_WIDTH+2-1)/6+1;
    logic [NUM_FRAC_LUTS-1:0] frac_overflow_parallel_ANDs;

    assign advance_round = unit_wb.ack | ~round_packet_r.valid;
    always_ff @ (posedge clk) begin
        if (advance_round)
            round_packet_r <= round_packet;
    end

    //compute mantissa overflow due to rounding in parallel with roundup addition
    assign hidden_round_frac_roundup = {hidden_round, frac, roundup};
    parallel_AND #(.WIDTH((FRAC_WIDTH+2-1)/6+1)) parallel_AND_inst(
        .i_data( {{(NUM_FRAC_LUTS*6-(FRAC_WIDTH+2)){1'b1}}, hidden_round_frac_roundup} ), 
        .o_data(frac_overflow_parallel_ANDs)
    );
    assign frac_overflow = &frac_overflow_parallel_ANDs;//&{hidden_round, frac, roundup};
    assert property (@(posedge clk) (frac_overflow|frac_overflow_debug) -> (frac_overflow_debug == frac_overflow));

    assign wb_valid = round_packet_r.valid;
    assign roundup = round_packet_r.roundup;
    assign sign_out = round_packet_r.data[FLEN-1];
    assign expo = round_packet_r.data[FLEN-2-:EXPO_WIDTH];
    assign expo_overflow_round = round_packet_r.expo_overflow;
    assign frac = round_packet_r.data[FRAC_WIDTH-1:0];
    assign hidden_round = round_packet_r.hidden;
    assign fflags = round_packet_r.fflags;

    assign {frac_overflow_debug, frac_round_intermediate} = {hidden_round, frac} + (FRAC_WIDTH+1)'(roundup);
    assign frac_out = frac_round_intermediate[FRAC_WIDTH-1:0] >> frac_overflow;
    assign overflowExp = (frac_overflow & &expo[EXPO_WIDTH-1:1]) | expo_overflow_round;
    assign expo_out = expo + EXPO_WIDTH'(frac_overflow);
    assign underflowExp = ~(hidden_round) & |frac_out;
    assign fflags_out = fflags[4] ? fflags : fflags | {2'b0, overflowExp, underflowExp, overflowExp}; //inexact is asserted when overflow 

    //Output
    assign unit_wb.id = round_packet_r.id;
    assign unit_wb.done = round_packet_r.valid;
    assign unit_wb.rd = overflowExp ? round_packet_r.result_if_overflow : {sign_out, expo_out, frac_out};
    assign unit_wb.fflags = fflags_out;

    function logic [FRAC_WIDTH+3+GRS_WIDTH-1:0] reverse(input logic signed [FRAC_WIDTH+3+GRS_WIDTH-1:0] in);
        foreach(in[i])
          reverse[i] = in[FRAC_WIDTH+3+GRS_WIDTH-1-i];
  endfunction

endmodule
