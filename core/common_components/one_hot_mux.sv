/*
 * Copyright © 2024 Chris Keilbart
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


module one_hot_mux
    #(
        parameter OPTIONS = 5,
        parameter type DATA_TYPE = logic
    )
    (
        //Only used for assertions
        input logic clk,
        input logic rst,

        input logic[OPTIONS-1:0] one_hot,
        input DATA_TYPE[OPTIONS-1:0] choices,
        output DATA_TYPE sel
    );

    //Casting to eliminate warnings
    typedef logic[$bits(DATA_TYPE)-1:0] casted_t;
    casted_t[OPTIONS-1:0] choices_casted;
    casted_t sel_casted;

    ////////////////////////////////////////////////////
    //Implementation
    //Cheaper than converting ohot -> int and indexing
    always_comb begin
        for (int i = 0; i < OPTIONS; i++)
            choices_casted[i] = casted_t'(choices[i]);
        sel = DATA_TYPE'(sel_casted);
    end

    generate if (OPTIONS == 1) begin : gen_no_mux
        assign sel_casted = choices_casted[0];
    end else begin : gen_mux
        always_comb begin
            sel_casted = '0;
            for (int i = 0; i < OPTIONS; i++)
                if (one_hot[i]) sel_casted |= choices_casted[i];
        end
    end endgenerate

    ////////////////////////////////////////////////////
    //Assertions
    ohot_assertion:
        assert property (@(posedge clk) disable iff (rst) $onehot0(one_hot))
        else $error("Selection mux not one hot");

endmodule
