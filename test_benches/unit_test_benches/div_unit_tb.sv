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
 *             Eric Matthews <ematthew@sfu.ca>
 *             Alec Lu <fla30@sfu.ca>
 */

`timescale 1ns / 1ps

import taiga_config::*;
import taiga_types::*;

typedef struct packed{
    div_inputs_t    module_input;
    logic [31: 0]   expected_result;
} div_result_t;

module div_unit_tb ();
    //DUT Regs and Wires
    logic                       clk;
    logic                       rst;
    logic                       gc_fetch_flush;
    unit_issue_interface        issue();
    unit_writeback_t            wb;
    div_inputs_t                div_inputs;
    //Internal Regs and Wires
    integer         test_number;
    //Input 
    integer         rs1_rand;
    integer         rs2_rand;
    int unsigned    rs1_urand;
    int unsigned    rs2_urand;
    integer         result_rand; 
    logic [ 1: 0]   op_rand;
    logic           reuse_rand;
    logic           accept;
    //Result
    div_result_t    result_queue[$];
    div_result_t    temp_result;
    //Latency
    parameter       MAX_RESPONSE_LATENCY = 32'hF;
    logic           wb_done;
    logic           firstPop;
    logic [31: 0]   latency_queue[$];
    logic [31: 0]   wb_done_acc;
    logic [31: 0]   response_latency;
    
    //DUT
    div_unit uut (.*);

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

    //With Latency
    //always_ff @(posedge clk) begin
    //    if (rst) begin
    //        wb_done_acc      <= 32'h1;
    //        firstPop         <= 1'b1;
    //        response_latency <= 32'hFFFFFFFF;
    //    end else begin
    //        if (wb.done) begin
    //            wb_done_acc <= wb_done_acc + 1;
    //        end else begin
    //            wb_done_acc <= 32'h1;
    //        end 
            
    //        if (firstPop | accept) begin
    //            response_latency <= latency_queue.pop_front();
    //            firstPop <= 1'b0;
    //        end else begin
    //            response_latency <= response_latency; 
    //        end             
    //    end 
    //end
    //always_ff @(posedge clk) begin
    //    if (rst)
    //       accept <= 0;
    //    else
    //       accept <= wb_done;
    //end
    //assign wb_done = wb.done & (wb_done_acc >= response_latency);

    //Without Latency
    assign wb_done = wb.done;
    assign accept = wb_done; 

    //Output checker
    always_ff @(posedge clk) begin
        if (rst)
            test_number <= 1;
        if (accept) begin
            test_number <= test_number + 1;
            temp_result = result_queue.pop_front();
            assert (wb.rd == temp_result.expected_result)
                else $error("Incorrect result on test number %d. (%h, should be: %h)\n\t Input: rs1: %d, rs2: %d, op: %b, reuse_result: %b", 
                    test_number, wb.rd, temp_result.expected_result,
                    temp_result.module_input.rs1, temp_result.module_input.rs2, 
                    temp_result.module_input.op, temp_result.module_input.reuse_result);
        end
    end

    //Driver
    task test_div (input integer a, b, result, latency, logic[1:0] op, logic reuse);
        wait (~clk & issue.ready);
        div_inputs.rs1 = a;
        div_inputs.rs2 = b;
        div_inputs.op = op;
        div_inputs.reuse_result = reuse;
        div_inputs.instruction_id = 0; //dont care
        result_queue.push_back({div_inputs, result});
        latency_queue.push_back(latency);
        issue.new_request = 1; #2
        issue.new_request = 0;
     endtask

    //Generator + Transaction
    task test_gen();
        op_rand = $urandom % 4;
        rs1_rand = $random;
        rs2_rand = $random;
        reuse_rand = 0;
        
        //SW model
        case (op_rand)
            2'b00:begin //Div
                if (rs2_rand == 0) begin
                  result_rand = -1;
                end else begin
                  result_rand = rs1_rand / rs2_rand;
                end
            end 
            2'b01:begin //uDiv 
                if (rs2_rand == 0) begin
                  result_rand = -1;
                end else begin
                  rs1_urand = rs1_rand;
                  rs2_urand = rs2_rand;
                  result_rand = rs1_urand / rs2_urand;
                end
            end 
            2'b10:begin //Rem
                if (rs2_rand == 0) begin
                  result_rand = rs1_rand;
                end else begin
                  result_rand = rs1_rand % rs2_rand;
                end
            end 
            2'b11:begin //uRem 
                if (rs2_rand == 0) begin
                  result_rand = rs1_rand;
                end else begin
                  rs1_urand = rs1_rand;
                  rs2_urand = rs2_rand;
                  result_rand = rs1_urand % rs2_urand;
                end
            end
        endcase  

        test_div (rs1_rand, rs2_rand, result_rand, genRandLatency(), op_rand, reuse_rand);
    endtask 

    initial
    begin
        clk = 0;
        rst = 1;
        gc_fetch_flush = 0;
        div_inputs.rs1 = 0;
        div_inputs.rs2 = 0;
        div_inputs.op = 0;
        div_inputs.reuse_result = 0;
        issue.new_request = 0;

        reset();
        
//        //Randomized Test (operation + latency)
//        for (int i=0; i < 5000; i = i+1) begin
//            test_gen();
//        end 

        for (int i=0; i < 6; i = i+5) begin
            //Div test
            test_div( 20,  6,  3,  i,  2'b00,  0);
            test_div(-20, -3,  6,  i,  2'b00,  0);
            test_div(-20,  6, -3,  i,  2'b00,  0);
            test_div( 20, -6, -3,  i,  2'b00,  0);
            test_div(-20, -6,  3,  i,  2'b00,  0);
    
            test_div(-1<<31,  1,  -1<<31,  i,  2'b00,  0);
            test_div(-1<<31, -1,  -1<<31,  i,  2'b00,  0);
    
            test_div(-1<<31, 0,  -1,  i,  2'b00,  0);
            test_div(-1,     0,  -1,  i,  2'b00,  0);
            test_div(0,      0,  -1,  i,  2'b00,  0);
    
            //uDiv test
            test_div( 20,  6,         3,  i,  2'b01,  0);
            test_div(-20,  6, 715827879,  i,  2'b01,  0);
            test_div( 20, -6,         0,  i,  2'b01,  0);
            test_div(-20, -6,         0,  i,  2'b01,  0);
    
            test_div(-1<<31,  1, -1<<31,  i,  2'b01,  0);
            test_div(-1<<31, -1,      0,  i,  2'b01,  0);
    
            test_div(-1<<31,  0,  -1,  i,  2'b01,  0);
            test_div(     1,  0,  -1,  i,  2'b01,  0);
            test_div(     0,  0,  -1,  i,  2'b01,  0);
    
            test_div(486456,   1,   486456,  i,  2'b01,  0);
            test_div(   200, 200,        1,  i,  2'b01,  0);
            test_div(234678,   2, 234678/2,  i,  2'b01,  0);
    
            //rem test
            test_div( 20,  6,  2,  i,  2'b10,  0);
            test_div(-20,  6, -2,  i,  2'b10,  0);
            test_div( 20, -6,  2,  i,  2'b10,  0);
            test_div(-20, -6, -2,  i,  2'b10,  0);
    
            test_div(-1<<31,  1, 0,  i,  2'b10,  0);
            test_div(-1<<31, -1, 0,  i,  2'b10,  0);
    
            test_div(-1<<31,  0, -1<<31,  i,  2'b10,  0);
            test_div(     1,  0,      1,  i,  2'b10,  0);
            test_div(     0,  0,      0,  i,  2'b10,  0);
    
            //remu test
            test_div( 20,  6,   2,  i,  2'b11,  0);
            test_div(-20,  6,   2,  i,  2'b11,  0);
            test_div( 20, -6,  20,  i,  2'b11,  0);
            test_div(-20, -6, -20,  i,  2'b11,  0);
    
            test_div(-1<<31,  1,      0,  i,  2'b11,  0);
            test_div(-1<<31, -1, -1<<31,  i,  2'b11,  0);
    
            test_div(-1<<31,  0, -1<<31,  i,  2'b11,  0);
            test_div(     1,  0,      1,  i,  2'b11,  0);
            test_div(     0,  0,      0,  i,  2'b11,  0);
            
            //reuse result tests
            test_div(20,  6,  2,  i,  2'b11,  0);
            test_div(20,  6,  2,  i,  2'b10,  1);
            test_div(20,  6,  3,  i,  2'b00,  1);
    
            test_div(200,  200,  1,  i,  2'b01,  0);
            test_div(200,  200,  1,  i,  2'b00,  1);
        end 
        
        wait (result_queue.size() == 0);
        //wait (latency_queue.size() == 0);
        #200;
        if (result_queue.size() == 0) begin
            // $display("queue size: %d", result_queue.size());
            
            case(DIV_ALGORITHM)
                RADIX_2 : $display("RADIX_2"); 
                RADIX_2_EARLY_TERMINATE : $display("RADIX_2_EARLY_TERMINATE"); 
                RADIX_2_EARLY_TERMINATE_FULL : $display("RADIX_2_EARLY_TERMINATE_FULL");
                RADIX_4 : $display("RADIX_4");
                RADIX_4_EARLY_TERMINATE : $display("RADIX_4_EARLY_TERMINATE");
                RADIX_8 : $display("RADIX_8");
                RADIX_8_EARLY_TERMINATE : $display("RADIX_8_EARLY_TERMINATE");
                RADIX_16 : $display("RADIX_16");
                QUICK_NAIVE : $display("QUICK_NAIVE");
                QUICK_CLZ : $display("QUICK_CLZ");
                QUICK_CLZ_MK2 : $display("QUICK_CLZ_MK2");
                QUICK_RADIX_4 : $display("QUCIK_RADIX_4");
                default : $error("invalid div selection");
            endcase
            $display("Div Unit Test -------------------- Passed");
        end
        $finish;
    end

endmodule
