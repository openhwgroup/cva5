/*
 * Copyright © 2017-2020 Yuhui Gao,  Lesley Shannon
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
 *             Yuhui Gao <yuhiug@sfu.ca>
 *             */

import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module fp_minmax (
    input logic clk,
    unit_issue_interface.unit issue,
    input fp_minmax_inputs_t fp_minmax_inputs,
    fp_unit_writeback_interface.unit wb
);
  
    ////////////////////////////////////////////////////
    //Implementation
    //See fp_preprocessing
    
    
    ////////////////////////////////////////////////////
    //Output
    assign wb.rd = fp_minmax_inputs.rs1;
    assign wb.hidden = fp_minmax_inputs.hidden;
    assign wb.fflags = {fp_minmax_inputs.invalid, 4'b0};
    assign wb.done = issue.new_request;
    assign wb.id = issue.id;
endmodule 
