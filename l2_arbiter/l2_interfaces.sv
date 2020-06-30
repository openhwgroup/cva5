/*
 * Copyright © 2017-2019 Eric Matthews,  Lesley Shannon
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

import l2_config_and_types::*;

interface l2_arbitration_interface;
    logic [L2_NUM_PORTS-1:0] requests;
    logic [$clog2(L2_NUM_PORTS)-1:0] grantee_i;
    logic [L2_NUM_PORTS-1:0] grantee_v;
    logic grantee_valid;
    logic strobe;

    modport slave (input requests, strobe, output grantee_i, grantee_v , grantee_valid);
    modport master (output requests, strobe, input grantee_i, grantee_v , grantee_valid);
endinterface
