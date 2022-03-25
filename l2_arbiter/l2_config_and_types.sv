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
 */


package l2_config_and_types;

    localparam L2_NUM_PORTS = 2;
    parameter L2_SUB_ID_W = 2; //Kept as parameter, due to localparam failing with scripted IP packaging


    //localparam int L2_INPUT_FIFO_DEPTHS [7 : 0]   = '{4, 4, 4, 4, 4, 4, 4, 4};
    //localparam int L2_INVALIDATION_FIFO_DEPTHS [7 : 0]   = '{4, 4, 4, 4, 4, 4, 4, 4};
    //localparam int L2_READ_RETURN_FIFO_DEPTHS [7 : 0]   = '{1, 1, 1, 1, 1, 1, 1, 1};//depth 1, rd_ack will be trimmed

    localparam L2_INPUT_FIFO_DEPTHS = 16;
    localparam L2_INVALIDATION_FIFO_DEPTHS = 16;
    localparam L2_READ_RETURN_FIFO_DEPTHS = 1;//depth 1, rd_ack will be trimmed


    localparam L2_MEM_ADDR_FIFO_DEPTH = 16;

    localparam L2_DATA_ATTRIBUTES_FIFO_DEPTH = 32;//Sized larger to remove need to check full status



    //Convenience derivative parameters
    localparam L2_ID_W = $clog2(L2_NUM_PORTS) + L2_SUB_ID_W;


    typedef struct packed{
        logic [29:0] addr;
        logic [3:0] be;
        logic rnw;
        logic is_amo;
        logic [4:0] amo_type_or_burst_size;
        logic [L2_SUB_ID_W-1:0] sub_id;
    } l2_request_t;

    typedef struct packed{
        logic [29:0] addr;
        logic [3:0] be;
        logic rnw;
        logic is_amo;
        logic [4:0] amo_type_or_burst_size;
        logic [L2_ID_W-1:0] id;
    } l2_mem_request_t;


    typedef struct packed{
        logic [$clog2(L2_NUM_PORTS)-1:0] id;
        logic [4:0] burst_size;
        logic abort_request;
    } l2_data_attributes_t;


    typedef struct packed{
        logic [$clog2(L2_NUM_PORTS)-1:0] id;
        logic [L2_SUB_ID_W-1:0] sub_id;
        logic [31:0] data;
    } l2_mem_return_data_t;

    typedef struct packed{
        logic [L2_SUB_ID_W-1:0] sub_id;
        logic [31:0] data;
    } l2_return_data_t;

endpackage


