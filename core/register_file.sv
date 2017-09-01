/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 * 
 * This Source Code Form is "Incompatible With Secondary Licenses", as
 * defined by the Mozilla Public License, v. 2.0.
 *
 * Initial code developed under the supervision of Dr. Lesley Shannon,
 * Reconfigurable Computing Lab, Simon Fraser University.
 *
 * Author(s):
 *             Eric Matthews <ematthew@sfu.ca>
 */
 
import taiga_config::*;
import taiga_types::*;

module register_file(
        input logic clk,
        input logic rst,
        input logic inorder,
        register_file_writeback_interface.unit rf_wb,
        register_file_decode_interface.unit rf_decode
        );

    (* ramstyle = "MLAB, no_rw_check" *) logic [XLEN-1:0] register [0:31];
    logic  inuse [0:31];
    (* ramstyle = "MLAB, no_rw_check" *) logic  [$clog2(INFLIGHT_QUEUE_DEPTH)-1:0] in_use_by [0:31];

    logic rs1_feedforward;
    logic rs2_feedforward;

    //End of signal declarations
    assign rs1_feedforward = (rf_decode.rs1_addr == rf_wb.rd_addr) && rf_wb.valid_write && (in_use_by[rf_wb.rd_addr] == rf_wb.id);
    assign rs2_feedforward = (rf_decode.rs2_addr == rf_wb.rd_addr) && rf_wb.valid_write && (in_use_by[rf_wb.rd_addr] == rf_wb.id);

    //Assign zero to r0 and initialize all registers to zero
    initial begin
        for (integer i=0; i<32; i=i+1) begin
            register[i] = '0;
            inuse[i] = 0;
            in_use_by[i] = '0;
        end
    end

    always_ff @ (posedge clk) begin
        if (rf_wb.valid_write && rf_wb.rd_addr != 0 && (in_use_by[rf_wb.rd_addr] == rf_wb.id || inorder)) //inorder needed for case when multiple outstanding writes to this register (common pattern: load, store, load) where the first load hasn't completed by the second causes an exception.  Without inorder we wouldn't commit the first load
            register[rf_wb.rd_addr] <= rf_wb.rd_data;
    end

    always_ff @ (posedge clk) begin
        if (rf_decode.instruction_issued && rf_decode.future_rd_addr != 0 )
            in_use_by[rf_decode.future_rd_addr] <= rf_decode.id;
    end

    genvar i;
    generate
        for (i= 1; i < 32; i=i+1) begin : inuse_g
            always_ff @ (posedge clk) begin
                if (rst)
                    inuse[i] <= 0;
                else if (rf_decode.instruction_issued && rf_decode.future_rd_addr == i)
                    inuse[i] <= 1;
                else if ( rf_wb.valid_write && (rf_wb.rd_addr == i) && (in_use_by[rf_wb.rd_addr] == rf_wb.id))//  || inorder <-- when exception has occurred
                    inuse[i] <= 0;
            end
        end
    endgenerate

    assign rf_decode.rs1_data = rs1_feedforward ? rf_wb.rd_data : register[rf_decode.rs1_addr];
    assign rf_decode.rs2_data = rs2_feedforward ? rf_wb.rd_data : register[rf_decode.rs2_addr];

    assign rf_decode.rs1_conflict = inuse[rf_decode.rs1_addr]  & ~rs1_feedforward;
    assign rf_decode.rs2_conflict = inuse[rf_decode.rs2_addr]  & ~rs2_feedforward;

endmodule
