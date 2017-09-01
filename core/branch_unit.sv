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

module branch_unit(
        input logic clk,
        input logic rst,

        func_unit_ex_interface.unit branch_ex,
        input branch_inputs_t branch_inputs,
        branch_table_interface.branch_unit bt,
        ras_interface.branch_unit ras,

        unit_writeback_interface.unit branch_wb
        );

    logic result;
    logic equal;
    logic lessthan;

    logic equal_ex;
    logic lessthan_ex;

    logic [XLEN:0] sub_result;
    logic [31:0] pc_offset;
    logic [2:0] fn3_ex;
    logic[31:0] rd_ex;

    logic [31:0] jump_count;
    logic [31:0] call_count;
    logic [31:0] ret_count;
    logic [31:0] br_count;

    logic jump_ex;
    logic bcomp_ex;

    logic done;
    logic new_jal_jalr_dec;

    assign equal = (branch_inputs.rs1 == branch_inputs.rs2);
    //  assign sub_result = signed'({branch_inputs.rs1[XLEN-1] & branch_inputs.use_signed, branch_inputs.rs1}) - signed'({branch_inputs.rs2[XLEN-1] & branch_inputs.use_signed, branch_inputs.rs2});
    assign lessthan = signed'({branch_inputs.rs1[XLEN-1] & branch_inputs.use_signed, branch_inputs.rs1}) <
        signed'({branch_inputs.rs2[XLEN-1] & branch_inputs.use_signed, branch_inputs.rs2});

    //  sub_result[XLEN];

    always_comb begin
        unique case (fn3_ex) // <-- 010, 011 unused
            BEQ_fn3 : result = equal_ex;
            BNE_fn3 : result = ~equal_ex;
            BLT_fn3 : result = lessthan_ex;
            BGE_fn3 : result = ~lessthan_ex;
            BLTU_fn3 : result = lessthan_ex;
            BGEU_fn3 : result = ~lessthan_ex;
        endcase
    end

    assign  bt.branch_taken =  (bcomp_ex & result) | jump_ex;

    always_comb begin
        if (branch_inputs.jal)
            pc_offset = 32'(signed'({branch_inputs.jal_imm, 1'b0}));
        else if (branch_inputs.jalr)
            pc_offset = 32'(signed'(branch_inputs.jalr_imm));
        else
            pc_offset = 32'(signed'({branch_inputs.br_imm, 1'b0}));
    end

    assign bt.prediction_dec = branch_inputs.prediction;


    assign bt.branch_ex = branch_ex.new_request;
    always_ff @(posedge clk) begin
        if (branch_ex.new_request_dec) begin
            fn3_ex <= branch_inputs.fn3;
            equal_ex <= equal;
            lessthan_ex <= lessthan;
            bt.ex_pc <= branch_inputs.dec_pc;
            bcomp_ex <= branch_inputs.branch_compare;
            jump_ex <= branch_inputs.jal | branch_inputs.jalr;
            bt.jump_pc <= (branch_inputs.jalr ? branch_inputs.rs1 : branch_inputs.dec_pc) + signed'(pc_offset);
            bt.njump_pc <= branch_inputs.dec_pc + 4;
            //bt.prediction_dec <= branch_inputs.prediction;

        end
    end


    assign new_jal_jalr_dec = branch_ex.new_request_dec & (branch_inputs.jal | branch_inputs.jalr)  & ~branch_inputs.rdx0;

    always_ff @(posedge clk) begin
        if (new_jal_jalr_dec) begin
            rd_ex <= branch_inputs.dec_pc + 4;
        end
    end

    /*********************************
     *  RAS support
     *********************************/
    logic rs1_link, rs1_eq_rd, rd_link;
    logic is_call;
    logic is_return;

    assign rs1_link = (branch_inputs.rs1_addr ==?  5'b00?01);
    assign rd_link = (branch_inputs.rd_addr ==?  5'b00?01);
    assign rs1_eq_rd = (branch_inputs.rs1_addr == branch_inputs.rd_addr);

    always_ff @(posedge clk) begin
        if (branch_ex.new_request_dec) begin
            is_call <= ( (branch_inputs.jal & rd_link) |  (branch_inputs.jalr & rd_link) );
            is_return <= ( (branch_inputs.jalr & ((rs1_link & ~rd_link) | (rs1_link & rd_link & ~rs1_eq_rd))) );
        end
    end

    assign ras.push = is_call & branch_ex.new_request;
    assign ras.pop = is_return & branch_ex.new_request;
    assign ras.new_addr = rd_ex;
    assign bt.is_return_ex = is_return;

    /*********************************
     *  Output
     *********************************/
    assign branch_ex.ready = ~done | (done & branch_wb.accepted);

    assign branch_wb.rd =  rd_ex;

    always_ff @(posedge clk) begin
        if (rst) begin
            done <= 0;
        end else if (new_jal_jalr_dec) begin
            done <= 1;
        end else if (branch_wb.accepted) begin
            done <= 0;
        end
    end

    assign branch_wb.done = done;
    assign branch_wb.early_done =  new_jal_jalr_dec | (done & ~branch_wb.accepted);

    /*********************************************/

//---------- Simulation counters
//    always_ff @(posedge clk) begin
//        if (rst) begin
//            jump_count <= 0;
//        end else if (branch_ex.new_request & jump_ex & ~is_call & ~is_return) begin
//            jump_count <= jump_count+1;
//        end
//    end

//    always_ff @(posedge clk) begin
//        if (rst) begin
//            call_count <= 0;
//        end else if (is_call & branch_ex.new_request) begin
//            call_count <= call_count+1;
//        end
//    end

//    always_ff @(posedge clk) begin
//        if (rst) begin
//            ret_count <= 0;
//        end else if (is_return & branch_ex.new_request) begin
//            ret_count <= ret_count+1;
//        end
//    end

//    always_ff @(posedge clk) begin
//        if (rst) begin
//            br_count <= 0;
//        end else if (branch_ex.new_request_dec & branch_inputs.branch_compare) begin
//            br_count <= br_count+1;
//        end
//    end


endmodule
