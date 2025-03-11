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

module plic_gateway

    #(
        parameter int unsigned NUM_IRQS = 1
    ) (
        input logic clk,
        input logic rst,

        input logic[NUM_IRQS-1:0] irq,
        input logic[NUM_IRQS-1:0] edge_sensitive, //Both rising and falling edges, else level sensitive and active high
        input logic[NUM_IRQS-1:0] claim,
        input logic[NUM_IRQS-1:0] complete,
        output logic[NUM_IRQS-1:0] ip
    );

    ////////////////////////////////////////////////////
    //PLIC Gateway
    //Registers interrupts, for them to be later claimed and completed

    //Raising
    logic[NUM_IRQS-1:0] irq_r;
    always_ff @(posedge clk) irq_r <= irq;

    logic[NUM_IRQS-1:0] raise;
    always_comb begin
        for (int i = 0; i < NUM_IRQS; i++)
            raise[i] = edge_sensitive[i] ? irq[i] ^ irq_r[i] : irq[i];
    end

    //Registering
    logic[NUM_IRQS-1:0] in_progress;
    always_ff @(posedge clk) begin
        if (rst) begin
            ip <= '0;
            in_progress <= '0;
        end
        else begin
            ip <= (ip | raise) & ~in_progress & ~claim;
            in_progress <= (in_progress | claim) & ~complete;
        end
    end

endmodule
