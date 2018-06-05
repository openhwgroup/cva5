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
    mul_inputs_t    module_input;
    logic [31: 0]   expected_result;
} mul_result_t;

module mul_unit_tb();
    //DUT Regs and Wires
    logic                       clk;
    logic                       rst;
    func_unit_ex_interface      mul_ex();
    unit_writeback_interface    mul_wb();
    mul_inputs_t                mul_inputs;

    //Internal Regs and Wires
    integer             test_number;
    //Input 
    int                 rs1_rand;
    int                 rs2_rand;
    int unsigned        rs1_urand;
    int unsigned        rs2_urand;
    longint             signedMulResult;
    longint unsigned    unsignedMulResult;
    logic [31: 0]       result_rand; 
    logic [ 1: 0]       op_rand;
    //Result
    mul_result_t        result_queue[$];
    mul_result_t        temp_result;
    //Latency
    parameter           MAX_RESPONSE_LATENCY = 32'hF;
    logic               wb_done;
    logic               firstPop;
    logic [31: 0]       latency_queue[$];
    logic [31: 0]       wb_done_acc;
    logic [31: 0]       response_latency;
    
    //DUT
    mul_unit uut (.*);
    
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
            if (mul_wb.done_next_cycle) begin
                wb_done_acc <= wb_done_acc + 1;
            end else begin
                wb_done_acc <= 32'h1;
            end 
            
            if (firstPop | mul_wb.accepted) begin
                response_latency <= latency_queue.pop_front();
                firstPop <= 1'b0;
            end else begin
                response_latency <= response_latency; 
            end             
        end 
    end
    
    assign wb_done = mul_wb.done_next_cycle & (wb_done_acc >= response_latency);

    always_ff @(posedge clk) begin
        if (rst)
           mul_wb.accepted <= 0;
        else
           mul_wb.accepted <= wb_done;
    end

    //Output checker
    always_ff @(posedge clk) begin
        if (rst)
            test_number <= 1;
        if (mul_wb.accepted) begin
            test_number <= test_number + 1;
            temp_result = result_queue.pop_front();
            if (temp_result.expected_result != 32'hxxxxxxxx) begin
                assert (mul_wb.rd == temp_result.expected_result)
                    else $error("Incorrect result on test number %d. (%h, should be: %h)\n\t Input: rs1: %d, rs2: %d, op: %b", 
                        test_number, mul_wb.rd, temp_result.expected_result,
                        temp_result.module_input.rs1, temp_result.module_input.rs2,
                        temp_result.module_input.op);
            end
        end
    end

    //Driver
    task test_div (input logic [XLEN-1:0] a, b, result, latency, logic[1:0] op);
        wait (~clk & mul_ex.ready);
        mul_inputs.rs1 = a;
        mul_inputs.rs2 = b;
        mul_inputs.op = op;
        result_queue.push_back({mul_inputs, result});
        latency_queue.push_back(latency);
        mul_ex.new_request_dec = 1; #2
        mul_ex.new_request_dec = 0;
     endtask

    //Generator + Transaction
    task test_gen();
        op_rand = $urandom % 4;
        rs1_rand = $random;
        rs2_rand = $random;
        
        //SW model
        case (op_rand)
            2'b00:begin //MUL
                signedMulResult = rs1_rand * rs2_rand;
                result_rand = signedMulResult[31: 0];
            end 
            2'b01:begin //MULH
                signedMulResult = rs1_rand * rs2_rand;
                result_rand = signedMulResult[63:32]; 
            end 
            2'b10:begin //MULHSU - rs1(signed) & rs2(unsigned)
                if (rs1_rand[31]) begin
                    rs1_urand = rs1_rand * -1;
                    rs2_urand = rs2_rand;
                    unsignedMulResult = rs1_urand * rs2_urand;
                    signedMulResult  = unsignedMulResult;
                    signedMulResult = signedMulResult * -1;
                    result_rand = signedMulResult[63:32];                   
                end else begin
                    rs1_urand = rs1_rand;
                    rs2_urand = rs2_rand;
                    unsignedMulResult = rs1_urand * rs2_urand;
                    result_rand = unsignedMulResult[63:32]; 
                end 
            end 
            2'b11:begin //MULHU
                rs1_urand = rs1_rand;
                rs2_urand = rs2_rand;
                unsignedMulResult = rs1_urand * rs2_urand;
                result_rand = unsignedMulResult[63:32];
            end
        endcase  

        test_div (rs1_rand, rs2_rand, result_rand, genRandLatency(), op_rand);
    endtask 

    initial
    begin
        clk = 0;
        rst = 1;
        mul_inputs.rs1 = 0;
        mul_inputs.rs2 = 0;
        mul_inputs.op = 0;
        mul_ex.new_request_dec = 0;
        mul_wb.accepted = 0;

        reset();
        
        //Randomized Test (operation + latency)
        for (int i=0; i < 1000; i = i+1) begin
            test_gen();
        end

        for (int i=0; i < 6; i = i+5) begin
            //MUL
            test_div (32'h00007e00, 32'hb6db6db7, 32'h00001200, i, 2'b00);
            test_div (32'h00007fc0, 32'hb6db6db7, 32'h00001240, i, 2'b00);
            
            test_div (32'h00000000, 32'h00000000, 32'h00000000, i, 2'b00);
            test_div (32'h00000001, 32'h00000001, 32'h00000001, i, 2'b00);
            test_div (32'h00000003, 32'h00000007, 32'h00000015, i, 2'b00);
            
            test_div (32'hffff8000, 32'h00000000, 32'h00000000, i, 2'b00);
            test_div (32'h00000000, 32'h80000000, 32'h00000000, i, 2'b00);
            test_div (32'hffff8000, 32'h80000000, 32'h00000000, i, 2'b00);
            
            test_div (32'haaaaaaab, 32'h0002fe7d, 32'h0000ff7f, i, 2'b00);
            test_div (32'h0002fe7d, 32'haaaaaaab, 32'h0000ff7f, i, 2'b00);
            
            test_div (32'hff000000, 32'hff000000, 32'h00000000, i, 2'b00);
            
            test_div (32'hffffffff, 32'hffffffff, 32'h00000001, i, 2'b00);
            test_div (32'h00000001, 32'hffffffff, 32'hffffffff, i, 2'b00);
            test_div (32'hffffffff, 32'h00000001, 32'hffffffff, i, 2'b00);              
                   
            //MULH
            test_div (32'h00000000, 32'h00000000, 32'h00000000, i, 2'b01);
            test_div (32'h00000001, 32'h00000001, 32'h00000000, i, 2'b01);
            test_div (32'h00000003, 32'h00000007, 32'h00000000, i, 2'b01);
            
            test_div (32'h00000000, 32'hffff8000, 32'h00000000, i, 2'b01);
            test_div (32'h80000000, 32'h00000000, 32'h00000000, i, 2'b01);
            test_div (32'h80000000, 32'h00000000, 32'h00000000, i, 2'b01);
    
            test_div (32'haaaaaaab, 32'h0002fe7d, 32'hffff0081, i, 2'b01);
            test_div (32'h0002fe7d, 32'haaaaaaab, 32'hffff0081, i, 2'b01);
            
            test_div (32'hff000000, 32'hff000000, 32'h00010000, i, 2'b01);
            
            test_div (32'hffffffff, 32'hffffffff, 32'h00000000, i, 2'b01);
            test_div (32'hffffffff, 32'h00000001, 32'hffffffff, i, 2'b01);
            test_div (32'h00000001, 32'hffffffff, 32'hffffffff, i, 2'b01);
    
             //MULHSU - rs1(signed) & rs2(unsigned)
            test_div (32'h00000000, 32'h00000000, 32'h00000000, i, 2'b10);
            test_div (32'h00000001, 32'h00000001, 32'h00000000, i, 2'b10);
            test_div (32'h00000007, 32'h00000003, 32'h00000000, i, 2'b10);
            
            test_div (32'hffff8000, 32'h00000000, 32'h00000000, i, 2'b10);
            test_div (32'h00000000, 32'h80000000, 32'h00000000, i, 2'b10);
            test_div (32'h80000000, 32'hffff8000, 32'h80004000, i, 2'b10);
            
            test_div (32'haaaaaaab, 32'h0002fe7d, 32'hffff0081, i, 2'b10);
            test_div (32'h0002fe7d, 32'haaaaaaab, 32'h0001fefe, i, 2'b10);
            
            test_div (32'hff000000, 32'hff000000, 32'hff010000, i, 2'b10);
            
            test_div (32'hffffffff, 32'hffffffff, 32'hffffffff, i, 2'b10);
            test_div (32'hffffffff, 32'h00000001, 32'hffffffff, i, 2'b10);
            test_div (32'h00000001, 32'hffffffff, 32'h00000000, i, 2'b10);       
            
            //MULHU
            test_div (32'h00000000, 32'h00000000, 32'h00000000, i, 2'b11);
            test_div (32'h00000001, 32'h00000001, 32'h00000000, i, 2'b11);
            test_div (32'h00000003, 32'h00000007, 32'h00000000, i, 2'b11);
            
            test_div (32'hffff8000, 32'h00000000, 32'h00000000, i, 2'b11);
            test_div (32'h80000000, 32'h00000000, 32'h00000000, i, 2'b11);
            test_div (32'h80000000, 32'hffff8000, 32'h7fffc000, i, 2'b11);
            
            test_div (32'haaaaaaab, 32'h0002fe7d, 32'h0001fefe, i, 2'b11);
            test_div (32'h0002fe7d, 32'haaaaaaab, 32'h0001fefe, i, 2'b11);
            
            test_div (32'hff000000, 32'hff000000, 32'hfe010000, i, 2'b11);
            
            test_div (32'hffffffff, 32'hffffffff, 32'hfffffffe, i, 2'b11);
            test_div (32'hffffffff, 32'h00000001, 32'h00000000, i, 2'b11);
            test_div (32'h00000001, 32'hffffffff, 32'h00000000, i, 2'b11);
        end
        
        wait (result_queue.size() == 0);
        wait (latency_queue.size() == 0);
        #200;
        if (result_queue.size() == 0) begin
            // $display("queue size: %d", result_queue.size());
            $display("Mul Unit Test -------------------- Passed");
        end
        $finish;
    end

endmodule
