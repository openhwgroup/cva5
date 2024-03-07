/*
 * Copyright © 2019-2023 Yuhui Gao, Chris Keilbart, Lesley Shannon
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module fp_normalize_rounding_top

    import cva5_config::*;
    import fpu_types::*;
    import cva5_types::*;

    #(
        parameter int unsigned NUM_WB_UNITS = 4
    )(
        input logic clk,
        input logic rst,
        fp_intermediate_wb_interface.wb intermediate_wb[NUM_WB_UNITS-1:0], //Priority order highest to lowest
        unit_writeback_interface.unit wb,
        output fflags_t fflags
    );

    localparam SHIFT_WIDTH = 3+FRAC_WIDTH+GRS_WIDTH;

    function logic[SHIFT_WIDTH-1:0] reverse(input logic[SHIFT_WIDTH-1:0] in);
        foreach(in[i])
            reverse[i] = in[SHIFT_WIDTH-1-i];
    endfunction

    typedef struct packed {
        id_t id;
        logic valid;
        fp_t data;
        logic expo_overflow;
        fflags_t fflags;
        rm_t rm;
        logic d2s;
        logic carry;
        logic safe;
        logic hidden;
        grs_t grs;
        fp_shift_amt_t clz;
        logic subnormal;
        logic right_shift;
        fp_shift_amt_t right_shift_amt;
        logic ignore_max_expo;
    } fp_normalize_packet_t;

    typedef struct packed {
        logic valid;
        id_t id;
        fflags_t fflags;
        rm_t rm;
        logic d2s;
        logic sign_norm;
        expo_d_t expo_norm;
        logic expo_overflow_norm;
        logic right_shift;
        fp_shift_amt_t shift_amt;
        logic sp_overflow;
        logic[EXPO_WIDTH_F-1:0] sp_expo;
        logic[SHIFT_WIDTH-1:0] shifter_in;
    } fp_shift_packet_t;

    typedef struct packed {
        id_t id;
        logic valid;
        fp_t data;
        logic expo_overflow;
        logic hidden;
        rm_t rm;
        fflags_t fflags;
        logic d2s;
        logic round_lsb;
        logic[2:0] round_grs;
        logic[1:0] tiny_rs;
    } fp_round_packet_t;

    ////////////////////////////////////////////////////
    //Implementation
    //First chooses a writeback request
    //Then normalizes through shifting and rounds
    logic advance_norm;
    logic advance_shift;
    logic advance_round;
    fp_normalize_packet_t normalize_packet;
    fp_shift_packet_t shift_packet;
    fp_round_packet_t round_packet;

    ////////////////////////////////////////////////////
    //Writeback
    //Chooses a writeback request in descending priority order
    //First unpacks interface signals so they can be dynamically indexed
    logic[$clog2(NUM_WB_UNITS)-1:0] unit_sel;
    //TODO: false circular dependency because misc_wb2fp uses ack as ready
    //unit_done[2:0] -> unit_ack[3] -> wb2fp.ack -> wb2fp.ready -> issue_to[4] -> wb2fp.new_request -> unit_done[3]
    /* verilator lint_off UNOPTFLAT */
    logic[NUM_WB_UNITS-1:0] unit_ack;
    /* verilator lint_on UNOPTFLAT */
    id_t[NUM_WB_UNITS-1:0] unit_instruction_id;
    logic[NUM_WB_UNITS-1:0] unit_done;    
    fp_t[NUM_WB_UNITS-1:0] unit_rd;
    logic[NUM_WB_UNITS-1:0] unit_expo_overflow;
    fflags_t[NUM_WB_UNITS-1:0] unit_fflags;
    rm_t[NUM_WB_UNITS-1:0] unit_rm;
    logic[NUM_WB_UNITS-1:0] unit_carry;
    logic[NUM_WB_UNITS-1:0] unit_safe;
    logic[NUM_WB_UNITS-1:0] unit_hidden;
    grs_t[NUM_WB_UNITS-1:0] unit_grs;
    fp_shift_amt_t[NUM_WB_UNITS-1:0] unit_clz;
    logic[NUM_WB_UNITS-1:0] unit_right_shift;
    fp_shift_amt_t[NUM_WB_UNITS-1:0] unit_right_shift_amt;
    logic[NUM_WB_UNITS-1:0] unit_subnormal;
    logic[NUM_WB_UNITS-1:0] unit_ignore_max_expo;
    logic[NUM_WB_UNITS-1:0] unit_d2s;

    generate for (genvar i = 0; i < NUM_WB_UNITS; i++) begin : gen_unpack
        assign intermediate_wb[i].ack = unit_ack[i];
        assign unit_instruction_id[i] = intermediate_wb[i].id;
        assign unit_done[i] = intermediate_wb[i].done;
        assign unit_rd[i] = intermediate_wb[i].rd;
        assign unit_expo_overflow[i] = intermediate_wb[i].expo_overflow;
        assign unit_fflags[i] = intermediate_wb[i].fflags;
        assign unit_rm[i] = intermediate_wb[i].rm;
        assign unit_carry[i] = intermediate_wb[i].carry;
        assign unit_safe[i] = intermediate_wb[i].safe;
        assign unit_hidden[i] = intermediate_wb[i].hidden;
        assign unit_grs[i] = intermediate_wb[i].grs;
        assign unit_clz[i] = intermediate_wb[i].clz;
        assign unit_right_shift[i] = intermediate_wb[i].right_shift;
        assign unit_right_shift_amt[i] = intermediate_wb[i].right_shift_amt;
        assign unit_subnormal[i] = intermediate_wb[i].subnormal;
        assign unit_ignore_max_expo[i] = intermediate_wb[i].ignore_max_expo;
        assign unit_d2s[i] = intermediate_wb[i].d2s;
    end endgenerate

    //Per-ID muxes for commit buffer
    always_comb begin
        unit_sel = $bits(unit_sel)'(NUM_WB_UNITS-1); //Must default to lowest priority because any other units override
        for (int i = NUM_WB_UNITS-2; i >= 0; i--) begin
            if (unit_done[i])
                unit_sel = $bits(unit_sel)'(i);
        end

        unit_ack = '0;
        unit_ack[unit_sel] = advance_norm;
    end

    //Advance logic
    assign advance_norm = advance_shift | ~normalize_packet.valid;
    always_ff @(posedge clk) begin
        if (rst)
            normalize_packet.valid <= 0;
        else if (advance_norm)
            normalize_packet.valid <= |unit_done;

        if (advance_norm) begin
            normalize_packet.id <= unit_instruction_id[unit_sel];
            normalize_packet.data <= unit_rd[unit_sel];
            normalize_packet.expo_overflow <= unit_expo_overflow[unit_sel];
            normalize_packet.fflags <= unit_fflags[unit_sel];
            normalize_packet.rm <= unit_rm[unit_sel];
            normalize_packet.d2s <= unit_d2s[unit_sel];
            normalize_packet.carry <= unit_carry[unit_sel];
            normalize_packet.safe <= unit_safe[unit_sel];
            normalize_packet.hidden <= unit_hidden[unit_sel];
            normalize_packet.grs <= unit_grs[unit_sel];
            normalize_packet.clz <= unit_clz[unit_sel];
            normalize_packet.subnormal <= unit_subnormal[unit_sel];
            normalize_packet.right_shift <= unit_right_shift[unit_sel];
            normalize_packet.right_shift_amt <= unit_right_shift_amt[unit_sel];
            normalize_packet.ignore_max_expo <= unit_ignore_max_expo[unit_sel];
        end
    end

    ////////////////////////////////////////////////////
    //Normalization
    //Determine the shift amount and direction according to the exponent
    //Potentially flip the mantissa
    logic right_shift;
    logic dp_overflow;
    logic sp_overflow;
    fp_shift_amt_t shift_amt;
    expo_d_t dp_expo;
    expo_s_t sp_expo;
    logic[SHIFT_WIDTH-1:0] in_left;
    logic[SHIFT_WIDTH-1:0] in_right;

    fp_prenormalize normalize_inst(
        .single(normalize_packet.d2s),
        .right_shift_in(normalize_packet.right_shift),
        .overflow_in(normalize_packet.expo_overflow),
        .subnormal(normalize_packet.subnormal),
        .expo_in(normalize_packet.data.d.expo),
        .ignore_max_expo(normalize_packet.ignore_max_expo),
        .left_shift_amt(normalize_packet.clz),
        .right_shift_amt(normalize_packet.right_shift_amt),

        .right_shift_out(right_shift),
        .dp_overflow_out(dp_overflow),
        .sp_overflow_out(sp_overflow),
        .shift_amt_out(shift_amt),
        .dp_expo_out(dp_expo),
        .sp_expo_out(sp_expo)
    );

    //Shifter input
    assign in_right = {normalize_packet.carry, normalize_packet.safe, normalize_packet.hidden, normalize_packet.data.d.frac, normalize_packet.grs};
    assign in_left = reverse(in_right);

    //Advance logic
    assign advance_shift = advance_round | ~shift_packet.valid;
    always_ff @(posedge clk) begin
        if (rst)
            shift_packet.valid <= 0;
        else if (advance_shift)
            shift_packet.valid <= normalize_packet.valid;
        
        if (advance_shift) begin
            shift_packet.sign_norm <= normalize_packet.data.d.sign;
            shift_packet.rm <= normalize_packet.rm;
            shift_packet.id <= normalize_packet.id;
            shift_packet.fflags <= normalize_packet.fflags;
            shift_packet.d2s <= normalize_packet.d2s;
            shift_packet.right_shift <= right_shift;
            shift_packet.expo_overflow_norm <= dp_overflow;
            shift_packet.sp_overflow <= sp_overflow;
            shift_packet.shift_amt <= shift_amt;
            shift_packet.expo_norm <= dp_expo;
            shift_packet.sp_expo <= sp_expo;
            shift_packet.shifter_in <= right_shift ? in_right : in_left;
        end
    end

    ////////////////////////////////////////////////////
    //Shifting and Roundup
    //Extremely wide right shifter, output is flipped for left shifts
    //Extracts the bits used for determining rounding
    logic[SHIFT_WIDTH-1:0] shift_intermediate;
    logic[SHIFT_WIDTH-1:0] shift_final;
    grs_t grs_norm;
    frac_d_t frac_norm;
    logic round_lsb;
    logic[2:0] round_grs;
    logic[1:0] tiny_rs;

    assign shift_intermediate = shift_packet.shifter_in >> shift_packet.shift_amt;
    assign shift_final = shift_packet.right_shift ? shift_intermediate : reverse(shift_intermediate);
    assign grs_norm = shift_final[GRS_WIDTH-1:0];
    assign frac_norm = shift_final[GRS_WIDTH+FRAC_WIDTH-1:GRS_WIDTH];

    //Right shifts may lose sticky bits - keep track
    logic sticky;
    logic set_sticky;
    assign set_sticky = sticky & shift_packet.right_shift;
    fp_sticky_tracking #(.INPUT_WIDTH(SHIFT_WIDTH), .SHIFT_WIDTH(EXPO_WIDTH)) right_sticky (
        .shifter_input(shift_packet.shifter_in),
        .shift_amount(shift_packet.shift_amt),
        .sticky_bit(sticky)
    );

    //GRS extraction for rounding
    //RISC-V specifies that tininess must be detected after rounding, as opposed to before. They only differ on underflow for +-2^-EMIN.
    //IEEE 754 states that we must therefore determine tininess as if the exponent range was unbounded (but not the fraction)
    //Therefore, we must undo the right shift of 1 to fit the exponent range when determining the roundup
    always_comb begin
        if (shift_packet.d2s) begin
            round_lsb = frac_norm[FRAC_WIDTH-FRAC_WIDTH_F];
            round_grs[2:1] = frac_norm[FRAC_WIDTH-FRAC_WIDTH_F-1-:2];
            round_grs[0] = |frac_norm[FRAC_WIDTH-FRAC_WIDTH_F-3:0] | |grs_norm | set_sticky;
            tiny_rs[1] = frac_norm[FRAC_WIDTH-FRAC_WIDTH_F-3];
            tiny_rs[0] = |frac_norm[FRAC_WIDTH-FRAC_WIDTH_F-4:0] | |grs_norm | set_sticky;
        end
        else begin
            round_lsb = frac_norm[0];
            round_grs[2:1] = grs_norm[GRS_WIDTH-1-:2];
            round_grs[0] = |grs_norm[GRS_WIDTH-3:0] | set_sticky;
            tiny_rs[1] = grs_norm[GRS_WIDTH-3];
            tiny_rs[0] = |grs_norm[GRS_WIDTH-4:0] | set_sticky;
        end
    end

    //Advance logic
    assign advance_round = wb.ack | ~round_packet.valid;
    always_ff @ (posedge clk) begin
        if (rst)
            round_packet.valid <= 0;
        else if (advance_round)
            round_packet.valid <= shift_packet.valid;

        if (advance_round) begin
            round_packet.hidden <= shift_final[GRS_WIDTH+FRAC_WIDTH];
            round_packet.id <= shift_packet.id;
            round_packet.rm <= shift_packet.rm;
            round_packet.d2s <= shift_packet.d2s;
            round_packet.round_lsb <= round_lsb;
            round_packet.round_grs <= round_grs;
            round_packet.tiny_rs <= tiny_rs;
            round_packet.data.d.sign <= shift_packet.sign_norm;
            round_packet.fflags.nv <= shift_packet.fflags.nv;
            round_packet.fflags.dz <= shift_packet.fflags.dz;
            round_packet.fflags.of <= shift_packet.fflags.of;
            round_packet.fflags.uf <= shift_packet.fflags.uf;
            round_packet.fflags.nx <= shift_packet.fflags.nx | |round_grs;

            if (shift_packet.d2s) begin
                round_packet.expo_overflow <= shift_packet.sp_overflow;
                round_packet.data.d.expo <= {{(EXPO_WIDTH-EXPO_WIDTH_F){1'b1}}, shift_packet.sp_expo}; //Allow the roundup to propagate to overflow
                round_packet.data.d.frac <= {frac_norm[FRAC_WIDTH-1-:FRAC_WIDTH_F], {(FRAC_WIDTH-FRAC_WIDTH_F){1'b1}}};
            end
            else begin
                round_packet.expo_overflow <= shift_packet.expo_overflow_norm;
                round_packet.data.d.expo <= shift_packet.expo_norm;
                round_packet.data.d.frac <= frac_norm;
            end
        end
    end

    ////////////////////////////////////////////////////
    //Rounding
    //Perform the rounding by adding based on the saved bits from the previous cycle
    //Also detects overflow
    logic frac_overflow;
    frac_d_t frac_out;
    expo_d_t expo_out;
    logic overflow_exp;
    fp_t rd;
    logic roundup;
    logic roundup_tiny;
    fp_t result_if_overflow;

    fp_roundup real_round (
        .sign(round_packet.data.d.sign),
        .rm(round_packet.rm),
        .grs(round_packet.round_grs),
        .lsb(round_packet.round_lsb),
        .roundup(roundup),
        .result_if_overflow(result_if_overflow)
    );

    fp_roundup tininess_round (
        .sign(round_packet.data.d.sign),
        .rm(round_packet.rm),
        .grs({round_packet.round_grs[1], round_packet.tiny_rs}),
        .lsb(round_packet.round_grs[2]),
        .roundup(roundup_tiny),
        .result_if_overflow()
    );

    assign {frac_overflow, frac_out} = round_packet.data.d.frac + (FRAC_WIDTH)'(roundup);
    assign expo_out = round_packet.data.d.expo + EXPO_WIDTH'(frac_overflow);

    //Compute exponent overflow due to rounding in parallel with roundup addition
    assign overflow_exp = (frac_overflow & &round_packet.data.d.expo[EXPO_WIDTH-1:1]) | round_packet.expo_overflow;

    //Output
    assign wb.id = round_packet.id;
    assign wb.done = round_packet.valid;
    assign wb.rd = rd.raw;
    always_comb begin
        if (overflow_exp) begin
            //Convert dp overflow value to sp
            if (round_packet.d2s) begin
                rd.s.box = '1;
                rd.s.sign = result_if_overflow.d.sign;
                rd.s.expo = result_if_overflow.d.expo[EXPO_WIDTH_F-1:0];
                rd.s.frac = result_if_overflow.d.frac[FRAC_WIDTH_F-1:0];
            end
            else
                rd = result_if_overflow;
        end
        else if (round_packet.d2s) begin
            rd.s.box = '1;
            rd.s.sign = round_packet.data.d.sign;
            rd.s.expo = expo_out[EXPO_WIDTH_F-1:0];
            rd.s.frac = frac_out[FRAC_WIDTH-1-:FRAC_WIDTH_F];
        end
        else begin
            rd.d.sign = round_packet.data.d.sign;
            rd.d.expo = expo_out;
            rd.d.frac = frac_out;
        end
    end
    
    assign fflags.nv = round_packet.fflags.nv;
    assign fflags.dz = round_packet.fflags.dz;
    assign fflags.of = round_packet.fflags.of | ~round_packet.fflags.nv & overflow_exp;
    //Underflow only occurs if inexact
    assign fflags.uf = round_packet.fflags.uf | (~round_packet.fflags.nv & round_packet.fflags.nx & ~round_packet.hidden & (~frac_overflow | ~(round_packet.round_grs[2] & roundup_tiny)));
    //Overflow is inexact
    assign fflags.nx = round_packet.fflags.nx | ~round_packet.fflags.nv & overflow_exp;

endmodule
