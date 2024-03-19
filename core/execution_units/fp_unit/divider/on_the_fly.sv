/*
 * Copyright © 2023 Chris Keilbart, Lesley Shannon
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
 */

module on_the_fly

    import fpu_types::*;

    #(
        parameter WIDTH = 32
    )(
        input logic[WIDTH-1:0] current_Q,
        input logic[WIDTH-1:0] current_QM,
        input q_t q,
        output logic[WIDTH-1:0] next_Q,
        output logic[WIDTH-1:0] next_QM,
        output logic bad_quotient_digit //Only used for assertion
    );

    logic[1:0] qin;
    logic[1:0] qmin;
    always_comb begin
        bad_quotient_digit = 0;
        unique case (q)
            POS_TWO,
            NEG_TWO: begin
                qin = 2'b10;
                qmin = 2'b01;
            end
            NEG_ONE: begin
                qin = 2'b11;
                qmin = 2'b10;
            end
            ZERO: begin
                qin = 2'b00;
                qmin = 2'b11;
            end
            NEG_THREE,
            POS_ONE: begin
                qin = 2'b01;
                qmin = 2'b00;
            end
            default: begin
                qin = 2'bXX;
                qmin = 2'bXX;
                bad_quotient_digit = 1;
            end
        endcase
    end

    always_comb begin
        if (q == NEG_TWO || q == NEG_ONE || q == NEG_THREE)
            next_Q = {current_QM[WIDTH-3:0], qin};
        else
            next_Q = {current_Q[WIDTH-3:0], qin};
        
        if (q == NEG_TWO || q == NEG_ONE || q == ZERO)
            next_QM = {current_QM[WIDTH-3:0], qmin};
        else
            next_QM = {current_Q[WIDTH-3:0], qmin};
    end

endmodule
