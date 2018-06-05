/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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
 *             Alec Lu <fla30@sfu.ca>
 *             Eric Matthews <ematthew@sfu.ca>
 */

`timescale 1ns / 1ps

import taiga_config::*;
import taiga_types::*;

typedef struct packed{
    alu_inputs_t    module_input;
    logic [31: 0]   expected_result;
} alu_result_t;

module alu_unit_tb();
    //DUT Regs and Wires
    logic                       clk;
    logic                       rst;
    func_unit_ex_interface      alu_ex();
    unit_writeback_interface    alu_wb();
    alu_inputs_t                alu_inputs;

    //Internal Regs and Wires
    integer             test_number;

    //Input
    logic [31: 0]       in1_rand;//contains sign padding bit for slt operation
    logic [31: 0]       in2_rand;//contains sign padding bit for slt operation
    logic               subtract_rand;
    logic               arith_rand;//contains sign padding bit for arithmetic shift right operation
    logic               lshift_rand;
    logic [ 2: 0]       fn3_rand;
    logic [ 1: 0]       op_rand;
    logic [31: 0]       result_rand;
    logic [32: 0]       result_rshift;
    logic [32: 0]       result_slt;

    //Result
    // logic [31: 0]       result_queue[$];
    // logic [31: 0]       temp_result;
    alu_result_t        result_queue[$];
    alu_result_t        temp_result;
    logic [31: 0]       alu_wb_rd_d;

    //Latency
    parameter           MAX_RESPONSE_LATENCY = 32'hF;
    logic               wb_done;
    logic               firstPop;
    logic [31: 0]       latency_queue[$];
    logic [31: 0]       wb_done_acc;
    logic [31: 0]       response_latency;

    //DUT
    alu_unit uut (.*);

    //Reset
    task reset;
        begin
            rst = 1'b1;
            #100 rst = 1'b0;
        end
    endtask

    //Clock Gen
    always
        #1 clk = ~clk;

            //Latency Logic
    function int genRandLatency();
        genRandLatency = $random & MAX_RESPONSE_LATENCY;
    endfunction

    always_ff @(posedge clk) begin
        if (rst) begin
            wb_done_acc      <= 32'h1;
            firstPop         <= 1'b1;
            response_latency <= 32'hFFFFFFFF;
        end else begin
            if (alu_wb.done_next_cycle) begin
                wb_done_acc <= wb_done_acc + 1;
            end else begin
                wb_done_acc <= 32'h1;
            end

            if (firstPop | alu_wb.accepted) begin
                response_latency <= latency_queue.pop_front();
                firstPop <= 1'b0;
            end else begin
                response_latency <= response_latency;
            end
        end
    end

    assign wb_done = alu_wb.done_next_cycle & (wb_done_acc >= response_latency);

    always_ff @(posedge clk) begin
        if (rst)
            alu_wb.accepted <= 0;
        else
            alu_wb.accepted <= wb_done;
    end

    //Output checker
    always_ff @(posedge clk) begin
        if (rst) begin
            alu_wb_rd_d <= 32'h0;
        end else begin
            alu_wb_rd_d <= alu_wb.rd;
        end
    end

    always_ff @(posedge clk) begin
        if (rst)
            test_number <= 1;
        if (alu_wb.accepted) begin
            test_number <= test_number + 1;
            temp_result = result_queue.pop_front();
            if (temp_result.expected_result != 32'hxxxxxxxx) begin
                assert (alu_wb_rd_d == temp_result.expected_result)
                    else $error("Incorrect result on test number %d. (%h, should be: %h)\n\t Input: in1: %d, in2: %d, subtract: %b, arith: %b, lshift: %b, shifter_in: %d, logic_op: %b, op: %b", 
                        test_number, alu_wb_rd_d, temp_result.expected_result,
                        temp_result.module_input.in1, temp_result.module_input.in2,
                        temp_result.module_input.subtract, temp_result.module_input.arith,
                        temp_result.module_input.lshift, temp_result.module_input.shifter_in,
                        temp_result.module_input.logic_op, temp_result.module_input.op);
            end
        end
    end

    //Driver
    task test_alu (
        input logic [XLEN:0]    in1,
        input logic [XLEN:0]    in2,
        input logic             subtract,
        input logic             arith,
        input logic             lshift,
        input logic [ 2: 0]     fn3,
        input logic [ 1: 0]     op,
        input logic [31: 0]     latency,
        input logic [XLEN-1:0]  result
        );
        wait (~clk & alu_ex.ready);
        alu_inputs.in1      = in1;
        alu_inputs.in2      = in2;
        alu_inputs.subtract = subtract;
        alu_inputs.arith    = arith;
        alu_inputs.lshift   = lshift;
        alu_inputs.shifter_in <= lshift ?  {<<{in1}} : in1;

        case (fn3)
            SLT_fn3 : alu_inputs.logic_op = ALU_LOGIC_ADD;
            SLTU_fn3 : alu_inputs.logic_op = ALU_LOGIC_ADD;
            SLL_fn3 : alu_inputs.logic_op = ALU_LOGIC_ADD;
            XOR_fn3 : alu_inputs.logic_op = ALU_LOGIC_XOR;
            OR_fn3 : alu_inputs.logic_op = ALU_LOGIC_OR;
            AND_fn3 : alu_inputs.logic_op = ALU_LOGIC_AND;
            SRA_fn3 : alu_inputs.logic_op = ALU_LOGIC_ADD;
            ADD_SUB_fn3 : alu_inputs.logic_op = ALU_LOGIC_ADD;
        endcase

        alu_inputs.op       = op;
        result_queue.push_back({alu_inputs, result});
        latency_queue.push_back(latency);
        alu_ex.new_request_dec = 1; #2
        alu_ex.new_request_dec = 0;
    endtask

    //Generator + Transaction
    task test_gen();
        //TODO: move all randomizing parameters out here
        op_rand = $urandom % 4;
        in1_rand = $random;
        in2_rand = $random;
        subtract_rand = $urandom % 2;
        fn3_rand = $urandom % 8;
        lshift_rand = $urandom % 2;
        arith_rand = $urandom % 2;

        //SW model
        case (op_rand)
            ALU_ADD_SUB: begin
                case (fn3_rand)
                    XOR_fn3 : begin result_rand = in1_rand ^ in2_rand; subtract_rand = 0; end
                    OR_fn3 : begin result_rand = in1_rand | in2_rand; subtract_rand = 0; end
                    AND_fn3 : begin result_rand = in1_rand & in2_rand; subtract_rand = 0; end
                    default : result_rand = subtract_rand ? in1_rand - in2_rand : in1_rand + in2_rand;
                endcase
            end
            ALU_SLT: begin
                subtract_rand = 1;
                fn3_rand = 0;
                result_slt = {1'b0, in1_rand} - {1'b0, in2_rand};
                result_rand = {31'b0, result_slt[32]};
            end
            default: begin //ALU_SHIFT
                if (lshift_rand) begin
                    arith_rand = 0;
                    result_rand = in1_rand << in2_rand[4:0];
                end else begin
                    result_rshift = signed'({arith_rand,in1_rand}) >>> in2_rand[4:0];
                    result_rand = result_rshift[31:0];
                end
            end
        endcase

        test_alu({1'b0, in1_rand}, {1'b0, in2_rand}, subtract_rand, arith_rand, lshift_rand, fn3_rand, op_rand, genRandLatency(), result_rand);
    endtask

    initial
    begin
        clk                     = 0;
        rst                     = 1;
        alu_inputs.in1          = 0;
        alu_inputs.in2          = 0;
        alu_inputs.subtract     = 0;
        alu_inputs.arith        = 0;
        alu_inputs.lshift       = 0;
        alu_inputs.logic_op     = 0;
        alu_inputs.op           = 0;
        alu_ex.new_request_dec  = 0;
        alu_wb.accepted         = 0;

        reset();

        for (int i=0; i < 6; i = i+5)
        begin
            //ALU_ADD_SUB = 2'b00,
            // Add
            test_alu(33'h00000000, 33'h00000000, 1'b0, 1'b0, 1'b0, 3'b000, 2'b00, i, 32'h00000000);
            test_alu(33'h00000001, 33'h00000001, 1'b0, 1'b0, 1'b0, 3'b000, 2'b00, i, 32'h00000002);
            test_alu(33'h00000003, 33'h00000007, 1'b0, 1'b0, 1'b0, 3'b000, 2'b00, i, 32'h0000000a);
            // Sub
            test_alu(33'h00000000, 33'h00000000, 1'b1, 1'b0, 1'b0, 3'b000, 2'b00, i, 32'h00000000);
            test_alu(33'h00000001, 33'h00000001, 1'b1, 1'b0, 1'b0, 3'b000, 2'b00, i, 32'h00000000);
            test_alu(33'h00000003, 33'h00000007, 1'b1, 1'b0, 1'b0, 3'b000, 2'b00, i, 32'hfffffffc);

            //ALU_LOGIC = 2'b01
            // AND
            test_alu(33'hff00ff00, 33'h0f0f0f0f, 1'b0, 1'b0, 1'b0, 3'b111, 2'b00, i, 32'h0f000f00);
            test_alu(33'h0ff00ff0, 33'hf0f0f0f0, 1'b0, 1'b0, 1'b0, 3'b111, 2'b00, i, 32'h00f000f0);
            test_alu(33'h00ff00ff, 33'h0f0f0f0f, 1'b0, 1'b0, 1'b0, 3'b111, 2'b00, i, 32'h000f000f);
            test_alu(33'hf00ff00f, 33'hf0f0f0f0, 1'b0, 1'b0, 1'b0, 3'b111, 2'b00, i, 32'hf000f000);
            // OR
            test_alu(33'hff00ff00, 33'h0f0f0f0f, 1'b0, 1'b0, 1'b0, 3'b110, 2'b00, i, 32'hff0fff0f);
            test_alu(33'h0ff00ff0, 33'hf0f0f0f0, 1'b0, 1'b0, 1'b0, 3'b110, 2'b00, i, 32'hfff0fff0);
            test_alu(33'h00ff00ff, 33'h0f0f0f0f, 1'b0, 1'b0, 1'b0, 3'b110, 2'b00, i, 32'h0fff0fff);
            test_alu(33'hf00ff00f, 33'hf0f0f0f0, 1'b0, 1'b0, 1'b0, 3'b110, 2'b00, i, 32'hf0fff0ff);
            // XOR
            test_alu(33'hff00ff00, 33'h0f0f0f0f, 1'b0, 1'b0, 1'b0, 3'b100, 2'b00, i, 32'hf00ff00f);
            test_alu(33'h0ff00ff0, 33'hf0f0f0f0, 1'b0, 1'b0, 1'b0, 3'b100, 2'b00, i, 32'hff00ff00);
            test_alu(33'h00ff00ff, 33'h0f0f0f0f, 1'b0, 1'b0, 1'b0, 3'b100, 2'b00, i, 32'h0ff00ff0);
            test_alu(33'hf00ff00f, 33'hf0f0f0f0, 1'b0, 1'b0, 1'b0, 3'b100, 2'b00, i, 32'h00ff00ff);

            //ALU_SLT = 2'b10
            // Add
            test_alu(33'h00000000, 33'h00000000, 1'b0, 1'b0, 1'b0, 3'b000, 2'b01, i, 32'h0);
            test_alu(33'h00000001, 33'h00000001, 1'b0, 1'b0, 1'b0, 3'b000, 2'b01, i, 32'h0);
            test_alu(33'h00000003, 33'h00000007, 1'b0, 1'b0, 1'b0, 3'b000, 2'b01, i, 32'h0);
            // Sub
            test_alu(33'h00000000, 33'h00000000, 1'b1, 1'b0, 1'b0, 3'b000, 2'b01, i, 32'h0);
            test_alu(33'h00000001, 33'h00000001, 1'b1, 1'b0, 1'b0, 3'b000, 2'b01, i, 32'h0);
            test_alu(33'h00000003, 33'h00000007, 1'b1, 1'b0, 1'b0, 3'b000, 2'b01, i, 32'h1);

            //ALU_SHIFT =2'b11
            // SLL
            test_alu(33'h00000001, 33'h00000000, 1'b0, 1'b0, 1'b1, 3'b000, 2'b10, i, 32'h00000001);
            test_alu(33'h00000001, 33'h00000001, 1'b0, 1'b0, 1'b1, 3'b000, 2'b10, i, 32'h00000002);
            test_alu(33'h00000001, 33'h00000007, 1'b0, 1'b0, 1'b1, 3'b000, 2'b10, i, 32'h00000080);
            test_alu(33'h00000001, 33'h0000000E, 1'b0, 1'b0, 1'b1, 3'b000, 2'b10, i, 32'h00004000);
            test_alu(33'h00000001, 33'h0000001F, 1'b0, 1'b0, 1'b1, 3'b000, 2'b10, i, 32'h80000000);
            test_alu(33'hffffffff, 33'h00000000, 1'b0, 1'b0, 1'b1, 3'b000, 2'b10, i, 32'hffffffff);
            test_alu(33'hffffffff, 33'h00000001, 1'b0, 1'b0, 1'b1, 3'b000, 2'b10, i, 32'hfffffffe);
            test_alu(33'hffffffff, 33'h00000007, 1'b0, 1'b0, 1'b1, 3'b000, 2'b10, i, 32'hffffff80);
            test_alu(33'hffffffff, 33'h0000000E, 1'b0, 1'b0, 1'b1, 3'b000, 2'b10, i, 32'hffffc000);
            test_alu(33'hffffffff, 33'h0000001F, 1'b0, 1'b0, 1'b1, 3'b000, 2'b10, i, 32'h80000000);
            test_alu(33'h21212121, 33'h00000000, 1'b0, 1'b0, 1'b1, 3'b000, 2'b10, i, 32'h21212121);
            test_alu(33'h21212121, 33'h00000001, 1'b0, 1'b0, 1'b1, 3'b000, 2'b10, i, 32'h42424242);
            test_alu(33'h21212121, 33'h00000007, 1'b0, 1'b0, 1'b1, 3'b000, 2'b10, i, 32'h90909080);
            test_alu(33'h21212121, 33'h0000000E, 1'b0, 1'b0, 1'b1, 3'b000, 2'b10, i, 32'h48484000);
            test_alu(33'h21212121, 33'h0000001F, 1'b0, 1'b0, 1'b1, 3'b000, 2'b10, i, 32'h80000000);
            // SRL
            test_alu(33'h80000000, 33'h00000000, 1'b0, 1'b0, 1'b0, 3'b000, 2'b10, i, 32'h80000000);
            test_alu(33'h80000000, 33'h00000001, 1'b0, 1'b0, 1'b0, 3'b000, 2'b10, i, 32'h40000000);
            test_alu(33'h80000000, 33'h00000007, 1'b0, 1'b0, 1'b0, 3'b000, 2'b10, i, 32'h01000000);
            test_alu(33'h80000000, 33'h0000000E, 1'b0, 1'b0, 1'b0, 3'b000, 2'b10, i, 32'h00020000);
            test_alu(33'h80000000, 33'h0000001F, 1'b0, 1'b0, 1'b0, 3'b000, 2'b10, i, 32'h00000001);
            test_alu(33'h7fffffff, 33'h00000000, 1'b0, 1'b0, 1'b0, 3'b000, 2'b10, i, 32'h7fffffff);
            test_alu(33'h7fffffff, 33'h00000001, 1'b0, 1'b0, 1'b0, 3'b000, 2'b10, i, 32'h3fffffff);
            test_alu(33'h7fffffff, 33'h00000007, 1'b0, 1'b0, 1'b0, 3'b000, 2'b10, i, 32'h00ffffff);
            test_alu(33'h7fffffff, 33'h0000000E, 1'b0, 1'b0, 1'b0, 3'b000, 2'b10, i, 32'h0001ffff);
            test_alu(33'h7fffffff, 33'h0000001F, 1'b0, 1'b0, 1'b0, 3'b000, 2'b10, i, 32'h00000000);
            test_alu(33'h81818181, 33'h00000000, 1'b0, 1'b0, 1'b0, 3'b000, 2'b10, i, 32'h81818181);
            test_alu(33'h81818181, 33'h00000001, 1'b0, 1'b0, 1'b0, 3'b000, 2'b10, i, 32'h40c0c0c0);
            test_alu(33'h81818181, 33'h00000007, 1'b0, 1'b0, 1'b0, 3'b000, 2'b10, i, 32'h01030303);
            test_alu(33'h81818181, 33'h0000000E, 1'b0, 1'b0, 1'b0, 3'b000, 2'b10, i, 32'h00020606);
            test_alu(33'h81818181, 33'h0000001F, 1'b0, 1'b0, 1'b0, 3'b000, 2'b10, i, 32'h00000001);
            // SRA
            test_alu(33'h80000000, 33'h00000000, 1'b0, 1'b1, 1'b0, 3'b000, 2'b10, i, 32'h80000000);
            test_alu(33'h80000000, 33'h00000001, 1'b0, 1'b1, 1'b0, 3'b000, 2'b10, i, 32'hc0000000);
            test_alu(33'h80000000, 33'h00000007, 1'b0, 1'b1, 1'b0, 3'b000, 2'b10, i, 32'hff000000);
            test_alu(33'h80000000, 33'h0000000E, 1'b0, 1'b1, 1'b0, 3'b000, 2'b10, i, 32'hfffe0000);
            test_alu(33'h80000000, 33'h0000001F, 1'b0, 1'b1, 1'b0, 3'b000, 2'b10, i, 32'hffffffff);
            test_alu(33'h81818181, 33'h00000000, 1'b0, 1'b1, 1'b0, 3'b000, 2'b10, i, 32'h81818181);
            test_alu(33'h81818181, 33'h00000001, 1'b0, 1'b1, 1'b0, 3'b000, 2'b10, i, 32'hc0c0c0c0);
            test_alu(33'h81818181, 33'h00000007, 1'b0, 1'b1, 1'b0, 3'b000, 2'b10, i, 32'hff030303);
            test_alu(33'h81818181, 33'h0000000E, 1'b0, 1'b1, 1'b0, 3'b000, 2'b10, i, 32'hfffe0606);
            test_alu(33'h81818181, 33'h0000001F, 1'b0, 1'b1, 1'b0, 3'b000, 2'b10, i, 32'hffffffff);
        end

        //Randomized Test (operation + latency)
        for (int i=0; i < 1000; i = i+1) begin
            test_gen();
        end

        wait (result_queue.size() == 0);
        wait (latency_queue.size() == 0);
        #200;
        if (result_queue.size() == 0) begin
            // $display("queue size: %d", result_queue.size());
            $display("ALU Unit Test -------------------- Passed");
        end
        $finish;
    end

endmodule

