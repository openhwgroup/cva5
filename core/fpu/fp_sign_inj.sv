/*
 * Copyright © 2019-2023 Yuhui Gao, Lesley Shannon
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
 *             Yuhui Gao <yuhuig@sfu.ca>
 */

module fp_sign_inj
    import fpu_types::*;

(
    input logic clk,
    unit_issue_interface.unit issue,
    input fp_sign_inject_inputs_t fp_sign_inject_inputs,
    fp_unit_writeback_interface.unit wb
);

    ////////////////////////////////////////////////////
    //Implementation
    //See pre processing
    
    ////////////////////////////////////////////////////
    //Output
    assign wb.rd = fp_sign_inject_inputs.rs1;
    assign wb.hidden = fp_sign_inject_inputs.hidden;
    assign wb.done = issue.new_request;
    assign wb.id = issue.id;
endmodule
