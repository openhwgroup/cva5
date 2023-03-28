/*
 * Copyright © 2019-2023 Yuhui Gao, Lesley Shannon
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
 *             Yuhui Gao <yuhuig@sfu.ca>
 */

module fp_normalize_rounding_top
    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    import fpu_types::*;

#(
    parameter int unsigned NUM_WB_UNITS = 3
)(
    input logic clk,
    input logic rst,
    fp_unit_writeback_interface.wb intermediate_unit_wb[NUM_WB_UNITS],
    fp_unit_writeback_interface.unit unit_wb
);

    //Writeback
    //aliases for write-back-interface signals
    logic [NUM_WB_UNITS-1:0] unit_ack;
    id_t [NUM_WB_UNITS-1:0] unit_instruction_id;
    logic [NUM_WB_UNITS-1:0] unit_done;
    logic [NUM_WB_UNITS-1:0][FLEN-1:0] unit_rd;
    logic [NUM_WB_UNITS-1:0] unit_carry;
    logic [NUM_WB_UNITS-1:0] unit_safe;
    logic [NUM_WB_UNITS-1:0] unit_hidden;
    logic [NUM_WB_UNITS-1:0] unit_expo_overflow;
    logic [NUM_WB_UNITS-1:0] unit_right_shift;
    logic [NUM_WB_UNITS-1:0] unit_subnormal;
    logic [NUM_WB_UNITS-1:0] unit_d2s;
    logic [NUM_WB_UNITS-1:0][2:0] unit_rm;
    logic [NUM_WB_UNITS-1:0][4:0] unit_fflags;
    fp_shift_amt_t [NUM_WB_UNITS-1:0] unit_clz;
    grs_t [NUM_WB_UNITS-1:0] unit_grs;
    logic [NUM_WB_UNITS-1:0][EXPO_WIDTH-1:0] unit_right_shift_amt;

    //Per-ID muxes for commit buffer
    logic [$clog2(NUM_WB_UNITS)-1:0] unit_sel;

    //Shared normalization
    fp_normalize_packet_t normalize_packet, normalize_packet_r;

    //Shared rounding
    fp_round_packet_t round_packet, round_packet_r;

    ////////////////////////////////////////////////////
    //Implementation
    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    generate
        for (genvar i = 0; i < NUM_WB_UNITS; i++) begin
            assign unit_instruction_id[i] = intermediate_unit_wb[i].id;
            assign unit_done[i] = intermediate_unit_wb[i].done;
            assign unit_rm[i] = intermediate_unit_wb[i].rm;
            assign unit_grs[i] = intermediate_unit_wb[i].grs;
            assign unit_carry[i] = intermediate_unit_wb[i].carry;
            assign unit_safe[i] = intermediate_unit_wb[i].safe;
            assign unit_hidden[i] = intermediate_unit_wb[i].hidden;
            assign unit_clz[i] = intermediate_unit_wb[i].clz;
            assign unit_subnormal[i] = intermediate_unit_wb[i].subnormal;
            assign unit_right_shift[i] = intermediate_unit_wb[i].right_shift;
            assign unit_right_shift_amt[i] = intermediate_unit_wb[i].right_shift_amt;
            assign unit_d2s[i] = intermediate_unit_wb[i].d2s;
            assign unit_rd[i] = intermediate_unit_wb[i].rd;
            assign unit_expo_overflow[i] = intermediate_unit_wb[i].expo_overflow;
            assign unit_fflags[i] = intermediate_unit_wb[i].fflags;
            assign intermediate_unit_wb[i].ack = unit_ack[i];
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Unit select for normalization module
    priority_encoder #(.WIDTH(NUM_WB_UNITS)) unit_done_encoder (
        .priority_vector(unit_done),
        .encoded_result(unit_sel)
    );

    always_comb begin
        //ID, data and rounding signals muxes
        normalize_packet.valid = |unit_done;
        normalize_packet.id = unit_instruction_id[unit_sel];
        normalize_packet.data = unit_rd[unit_sel];
        normalize_packet.expo_overflow = unit_expo_overflow[unit_sel];
        normalize_packet.fflags =  unit_fflags[unit_sel];
        normalize_packet.rm =  unit_rm[unit_sel];
        normalize_packet.d2s = unit_d2s[unit_sel];
        normalize_packet.carry = unit_carry[unit_sel];
        normalize_packet.safe = unit_safe[unit_sel];
        normalize_packet.hidden = unit_hidden[unit_sel];
        normalize_packet.grs = unit_grs[unit_sel];
        normalize_packet.clz = unit_clz[unit_sel];
        normalize_packet.subnormal = unit_subnormal[unit_sel];
        normalize_packet.right_shift = unit_right_shift[unit_sel];
        normalize_packet.right_shift_amt = unit_right_shift_amt[unit_sel];
        //Unit Ack
        unit_ack = '0;
        unit_ack[unit_sel] = advance_norm & normalize_packet.valid; //writeback not valid until the normalization stage is ready
    end

    ////////////////////////////////////////////////////
    //Shared normalzation
    logic [FLEN-1:0]             result_if_overflow;
    logic advance_norm;
    /* verilator lint_off UNOPTFLAT */ //TODO
    fp_normalize_pre_processing_packet_t normalize_pre_processing_packet;
    /* verilator lint_on UNOPTFLAT */

    assign advance_norm = advance_shift | ~normalize_packet_r.valid;
    always_ff @ (posedge clk) begin
        if (advance_norm)
            normalize_packet_r <= normalize_packet;
    end

    //normalization
    fp_prenormalize normalize_inst(
        .single(normalize_packet_r.d2s),
        .right_shift_in(normalize_packet_r.right_shift),
        .overflow_in(normalize_packet_r.expo_overflow),
        .subnormal(normalize_packet_r.subnormal),
        .hidden_bit(normalize_packet_r.hidden),
        .expo_in(normalize_packet_r.data[FLEN-2-:EXPO_WIDTH]),
        .left_shift_amt(normalize_packet_r.clz),
        .right_shift_amt(normalize_packet_r.right_shift_amt),

        .right_shift_out(normalize_pre_processing_packet.right_shift),
        .dp_overflow_out(normalize_pre_processing_packet.expo_overflow_norm),
        .sp_overflow_out(normalize_pre_processing_packet.sp_overflow),
        .shift_amt_out(normalize_pre_processing_packet.shift_amt),
        .dp_expo_out(normalize_pre_processing_packet.expo_norm),
        .sp_expo_out(normalize_pre_processing_packet.sp_expo)
    );
    assign normalize_pre_processing_packet.sign_norm = normalize_packet_r.data[FLEN-1];
    assign normalize_pre_processing_packet.valid = normalize_packet_r.valid;
    assign normalize_pre_processing_packet.rm = normalize_packet_r.rm;
    assign normalize_pre_processing_packet.id = normalize_packet_r.id;
    assign normalize_pre_processing_packet.fflags = normalize_packet_r.fflags;
    assign normalize_pre_processing_packet.d2s = normalize_packet_r.d2s;

    logic signed [FRAC_WIDTH+3+GRS_WIDTH-1:0] in_left;
    logic signed [FRAC_WIDTH+3+GRS_WIDTH-1:0] in_right;
    assign in_right = {normalize_packet_r.carry, normalize_packet_r.safe, normalize_packet_r.hidden, normalize_packet_r.data[FRAC_WIDTH-1:0], normalize_packet_r.grs};
    assign in_left = reverse(in_right);
    assign normalize_pre_processing_packet.shifter_in = normalize_pre_processing_packet.right_shift ? in_right : in_left;

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
        result_expo_norm = normalize_pre_processing_packet_r.d2s ? {{(EXPO_WIDTH-EXPO_WIDTH_F){normalize_pre_processing_packet_r.sp_expo[EXPO_WIDTH_F-1]}}, normalize_pre_processing_packet_r.sp_expo} : normalize_pre_processing_packet_r.expo_norm;
        expo_overflow_norm = normalize_pre_processing_packet_r.d2s ? normalize_pre_processing_packet_r.sp_overflow : normalize_pre_processing_packet_r.expo_overflow_norm;
    end

    assign advance_shift = advance_round | ~normalize_pre_processing_packet_r.valid;
    always_ff @ (posedge clk) begin
        if (advance_shift)
            normalize_pre_processing_packet_r <= normalize_pre_processing_packet;
    end

    logic[2:0] round_grs;
    assign round_grs = normalize_pre_processing_packet_r.d2s ? 
        {result_frac_norm[FRAC_WIDTH-FRAC_WIDTH_F-1 -: 2], |result_frac_norm[FRAC_WIDTH-FRAC_WIDTH_F-3:0] | |grs_norm} : 
        {grs_norm[GRS_WIDTH-1-:2], |grs_norm[0+:GRS_WIDTH-2]};
    logic round_lsb;
    assign round_lsb = normalize_pre_processing_packet_r.d2s ? result_frac_norm[FRAC_WIDTH-FRAC_WIDTH_F] : result_frac_norm[0];

    logic round_inexact;
    assign round_inexact = |round_grs;

    //roundup calculation
    fp_round_simplified round(
        .sign(result_sign_norm),
        .rm(normalize_pre_processing_packet_r.rm),
        .grs(round_grs),
        .lsb(round_lsb),
        .roundup(round_packet.roundup),
        .result_if_overflow(result_if_overflow)
    );

    //prep for rounding
    assign round_packet.valid = normalize_pre_processing_packet_r.valid;
    assign round_packet.data = {result_sign_norm, result_expo_norm, result_frac_norm};
    assign round_packet.expo_overflow = expo_overflow_norm;
    assign round_packet.hidden = hidden_norm;
    assign round_packet.id = normalize_pre_processing_packet_r.id;
    assign round_packet.result_if_overflow = normalize_pre_processing_packet_r.d2s ? {{(FLEN-FLEN_F){1'b1}}, result_if_overflow[FLEN-1], result_if_overflow[FRAC_WIDTH +: EXPO_WIDTH_F], result_if_overflow[FRAC_WIDTH_F-1:0]} : result_if_overflow; //Convert dp overflow value to sp
    assign round_packet.d2s = normalize_pre_processing_packet_r.d2s;
    assign round_packet.fflags = {normalize_pre_processing_packet_r.fflags[4:1], normalize_pre_processing_packet_r.fflags[0] | round_inexact};

    ////////////////////////////////////////////////////
    //Shared rounding
    logic [FRAC_WIDTH+1:0]       hidden_round_frac_roundup;
    logic [FRAC_WIDTH:0]         frac_round_intermediate;
    logic                        roundup;
    logic                        frac_overflow;
    logic                        sign_out;
    logic [EXPO_WIDTH-1:0]       expo, expo_out;
    logic                        expo_overflow_round;
    logic [FRAC_WIDTH-1:0]       frac, frac_out;
    logic                        hidden_round;
    logic [4:0]                  fflags, fflags_out;
    logic                        overflowExp, underflowExp;
    logic frac_overflow_debug;
    logic advance_round;
    logic round_d2s;

    assign advance_round = unit_wb.ack | ~round_packet_r.valid;
    always_ff @ (posedge clk) begin
        if (advance_round)
            round_packet_r <= round_packet;
    end

    //compute mantissa overflow due to rounding in parallel with roundup addition
    assign hidden_round_frac_roundup = {hidden_round, frac, roundup};
    assign frac_overflow = &hidden_round_frac_roundup;
    assert property (@(posedge clk) (frac_overflow|frac_overflow_debug) -> (frac_overflow_debug == frac_overflow));

    assign roundup = round_packet_r.roundup;
    assign sign_out = round_packet_r.data[FLEN-1];
    assign expo = round_packet_r.data[FLEN-2-:EXPO_WIDTH];
    assign expo_overflow_round = round_packet_r.expo_overflow;
    assign frac = round_d2s ? {round_packet_r.data[FRAC_WIDTH-1 -: FRAC_WIDTH_F], {(FRAC_WIDTH-FRAC_WIDTH_F){1'b1}}} : round_packet_r.data[FRAC_WIDTH-1:0];
    assign hidden_round = round_packet_r.hidden;
    assign fflags = round_packet_r.fflags;
    assign round_d2s = round_packet_r.d2s;

    assign {frac_overflow_debug, frac_round_intermediate} = {hidden_round, frac} + (FRAC_WIDTH+1)'(roundup);
    assign frac_out = frac_round_intermediate[FRAC_WIDTH-1:0] >> frac_overflow;
    assign overflowExp = (frac_overflow & &expo[EXPO_WIDTH-1:1]) | expo_overflow_round;
    assign expo_out = expo + EXPO_WIDTH'(frac_overflow);
    assign underflowExp = ~(hidden_round) & |frac_out & fflags[0]; //Underflow only occurs if inexact
    assign fflags_out = fflags[4] ? fflags : fflags | {2'b0, overflowExp, underflowExp, overflowExp}; //inexact is asserted when overflow

    //Output
    assign unit_wb.id = round_packet_r.id;
    assign unit_wb.done = round_packet_r.valid;
    always_comb begin
        if (overflowExp)
            unit_wb.rd = round_packet_r.result_if_overflow;
        else if (round_d2s)
            unit_wb.rd = {{(FLEN-FLEN_F){1'b1}}, sign_out, expo_out[0 +: EXPO_WIDTH_F], frac_out[FRAC_WIDTH-1 -: FRAC_WIDTH_F]};
        else
            unit_wb.rd = {sign_out, expo_out, frac_out};
    end
    assign unit_wb.fflags = fflags_out;

    function logic [FRAC_WIDTH+3+GRS_WIDTH-1:0] reverse(input logic signed [FRAC_WIDTH+3+GRS_WIDTH-1:0] in);
        foreach(in[i])
            reverse[i] = in[FRAC_WIDTH+3+GRS_WIDTH-1-i];
    endfunction

endmodule
