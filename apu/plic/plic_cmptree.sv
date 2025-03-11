/*
 * Copyright © 2024 Chris Keilbart, Mohammad Shahidzadeh
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 *             Mohammad Shahidzadeh <mohammad_shahidzadeh_asadi@sfu.ca>
 */

module plic_cmptree

    #(
        parameter int unsigned NUM_IRQS = 2,
        parameter int unsigned PRIORITY_W = 4,
        parameter int unsigned REG_STAGE_W = 2
    ) (
        input logic clk,

        input logic[NUM_IRQS-1:0] irq_valid,
        input logic[NUM_IRQS-1:0][PRIORITY_W-1:0] irq_priority,
        output logic[$clog2(NUM_IRQS)-1:0] highest_id,
        output logic[PRIORITY_W-1:0] highest_priority,
        output logic highest_valid
    );

    localparam ID_W = $clog2(NUM_IRQS);
    localparam PADDED_W = 2**ID_W;

    ////////////////////////////////////////////////////
    //PLIC Comparison Tree
    //The interrupt with the highest priority must be selected
    //Ties are broken by the index, with lower values taking priority
    //Implemented as a binary tree, and the outputs of a certain layer are registered

    //Pad to next power of two
    logic[PADDED_W-1:0] padded_irq_valid;
    logic[PADDED_W-1:0][PRIORITY_W-1:0] padded_irq_priority;

    always_comb begin
        for (int i = 0; i < PADDED_W; i++) begin
            padded_irq_valid[i] = i < NUM_IRQS ? irq_valid[i] : 1'b0;
            padded_irq_priority[i] = i < NUM_IRQS ? irq_priority[i] : '0;
        end
    end

    //Same no matter the stage
    logic left_valid;
    logic[PRIORITY_W-1:0] left_priority;
    logic right_valid;
    logic[PRIORITY_W-1:0] right_priority;
    logic chose_valid;
    logic chose_left;
    logic[PRIORITY_W-1:0] chose_priority;

    assign chose_valid = left_valid | right_valid;
    assign chose_left = left_valid & (~right_valid | left_priority > right_priority);
    assign chose_priority = chose_left ? left_priority : right_priority;


    //Recursive or base case
    generate if (NUM_IRQS == 2) begin : gen_base_case
        assign {left_valid, right_valid} = irq_valid;
        assign {left_priority, right_priority} = irq_priority;

        if (REG_STAGE_W == 2) begin : gen_ff
            always_ff @(posedge clk) begin
                highest_id[0] <= chose_left;
                highest_priority <= chose_priority;
                highest_valid <= chose_valid;
            end
        end else begin : gen_no_ff
            assign highest_id[0] = chose_left;
            assign highest_priority = chose_priority;
            assign highest_valid = chose_priority;
        end
    end else begin : gen_recursive_case
        logic[ID_W-2:0] left_id;
        plic_cmptree #(.NUM_IRQS(PADDED_W/2), .PRIORITY_W(PRIORITY_W), .REG_STAGE_W(REG_STAGE_W)) left_tree (
            .irq_valid(padded_irq_valid[PADDED_W-1:PADDED_W/2]),
            .irq_priority(padded_irq_priority[PADDED_W-1:PADDED_W/2]),
            .highest_id(left_id),
            .highest_priority(left_priority),
            .highest_valid(left_valid),
        .*);

        logic[ID_W-2:0] right_id;
        plic_cmptree #(.NUM_IRQS(PADDED_W/2), .PRIORITY_W(PRIORITY_W), .REG_STAGE_W(REG_STAGE_W)) right_tree (
            .irq_valid(padded_irq_valid[PADDED_W/2-1:0]),
            .irq_priority(padded_irq_priority[PADDED_W/2-1:0]),
            .highest_id(right_id),
            .highest_priority(right_priority),
            .highest_valid(right_valid),
        .*);

        if (REG_STAGE_W == NUM_IRQS) begin : gen_ff
            always_ff @(posedge clk) begin
                highest_id[ID_W-1] <= chose_left;
                highest_id[ID_W-2:0] <= chose_left ? left_id : right_id;
                highest_priority <= chose_priority;
                highest_valid <= chose_valid;
            end
        end else begin : gen_no_ff
            assign highest_id[ID_W-1] = chose_left;
            assign highest_id[ID_W-2:0] = chose_left ? left_id : right_id;
            assign highest_priority = chose_priority;
            assign highest_valid = chose_valid;
        end
    end endgenerate

endmodule
