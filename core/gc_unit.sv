/*
 * Copyright © 2018 Eric Matthews,  Lesley Shannon
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
 */

import taiga_config::*;
import taiga_types::*;

module gc_unit(
        input logic clk,
        input logic rst,
        input logic interrupt,
        func_unit_ex_interface.unit gc_ex,
        input gc_inputs_t gc_inputs,
        output logic gc_issue_hold,
        output logic gc_issue_flush,
        output logic gc_fetch_hold,
        output logic gc_fetch_flush,

        output logic inuse_clear
        );

    //Largest depth for TLBs
    localparam int TLB_CLEAR_DEPTH = (DTLB_DEPTH > ITLB_DEPTH) ? DTLB_DEPTH : ITLB_DEPTH;
    //For general reset clear, greater of TLB depth or inuse memory block (32-bits)
    localparam int CLEAR_DEPTH = USE_MMU ? TLB_CLEAR_DEPTH : 32;

    logic [CLEAR_DEPTH-1:0] clear_shift_count;
    logic [TLB_CLEAR_DEPTH-1:0] tlb_clear_shift_count;
    ////////////////////////////////////////////////////


    enum {RST_STATE, PRE_CLEAR_STATE, CLEAR_STATE, IDLE_STATE, TLB_CLEAR_STATE} state, next_state;


    //implementation
    ////////////////////////////////////////////////////
    always_ff @(posedge clk) begin
        if (rst)
            state <= RST_STATE;
        else
            state <= next_state;
    end

    always_comb begin
        next_state = state;
        case (state)
            RST_STATE : next_state = PRE_CLEAR_STATE;
            PRE_CLEAR_STATE : next_state = CLEAR_STATE;
            CLEAR_STATE : if (clear_shift_count[CLEAR_DEPTH-1]) next_state = IDLE_STATE;
            IDLE_STATE : if (interrupt) next_state = TLB_CLEAR_STATE;
            TLB_CLEAR_STATE : if (tlb_clear_shift_count[TLB_CLEAR_DEPTH-1]) next_state = IDLE_STATE;
            default : next_state = RST_STATE;
        endcase
    end


    assign gc_issue_hold = state inside {PRE_CLEAR_STATE, CLEAR_STATE, TLB_CLEAR_STATE};
    assign inuse_clear = state inside {CLEAR_STATE};

    assign gc_issue_flush = 0;
    assign gc_fetch_hold = 0;
    assign gc_fetch_flush = 0;

    //CLEAR state shift reg
    always_ff @ (posedge clk) begin
        clear_shift_count[0] <= (state == PRE_CLEAR_STATE) && (next_state == CLEAR_STATE);
        clear_shift_count[CLEAR_DEPTH-1:1] <= clear_shift_count[CLEAR_DEPTH-2:0];
    end
    //TLB_CLEAR state shift reg
    always_ff @ (posedge clk) begin
        tlb_clear_shift_count[0] <= (state == IDLE_STATE) && (next_state == TLB_CLEAR_STATE);
        tlb_clear_shift_count[TLB_CLEAR_DEPTH-1:1] <= tlb_clear_shift_count[TLB_CLEAR_DEPTH-2:0];
    end


    ////////////////////////////////////////////////////
    assign gc_ex.ready = 1;


    ////////////////////////////////////////////////////

endmodule
