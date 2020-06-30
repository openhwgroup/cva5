/*
 * Copyright © 2017-2020 Eric Matthews,  Lesley Shannon
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
import riscv_types::*;
import taiga_types::*;
import l2_config_and_types::*;

module l1_arbiter
        (
        input logic clk,
        input logic rst,

        l2_requester_interface.master l2,

        output sc_complete,
        output sc_success,

        l1_arbiter_request_interface.slave l1_request[L1_CONNECTIONS-1:0],
        l1_arbiter_return_interface.slave l1_response[L1_CONNECTIONS-1:0]
        );

    l2_request_t[L1_CONNECTIONS-1:0] l2_requests;

    logic [L1_CONNECTIONS-1:0] requests;
    logic [L1_CONNECTIONS-1:0] acks;

    logic push_ready;
    logic request_exists;


    //////////////////////////////////////
    genvar i;

    generate
        for (i=0; i <L1_CONNECTIONS; i++) begin
            assign requests[i] = l1_request[i].request;
            assign l1_request[i].ack = acks[i];
        end
    endgenerate

    generate
        if (USE_DCACHE && USE_DTAG_INVALIDATIONS)
            assign l2.inv_ack = l1_response[L1_DCACHE_ID].inv_ack;
        else
            assign l2.inv_ack = l2.inv_valid;
    endgenerate

    assign l2.rd_data_ack = l2.rd_data_valid;
    assign sc_complete = l2.con_valid;
    assign sc_success = l2.con_result;

    //arbiter can pop address FIFO at a different rate than the data FIFO, so check that both have space.
    assign push_ready = ~l2.request_full & ~l2.data_full;
    assign request_exists = |requests;

    assign l2.request_push = push_ready & request_exists;

    //priority 0-to-n
    logic busy;
    always_comb begin
        acks[0] = l1_request[0].request & push_ready;//L1_DCACHE_ID
        busy = l1_request[0].request;
        for (int i = 1; i < L1_CONNECTIONS; i++) begin
            acks[i] = requests[i] & push_ready & ~busy;
            busy |= requests[i];
        end
    end


    generate
        if (USE_DCACHE) begin
            assign l2.wr_data_push = push_ready & l1_request[L1_DCACHE_ID].request & ~l1_request[L1_DCACHE_ID].rnw; //Assumes data cache has highest priority
            assign l2.wr_data = l1_request[L1_DCACHE_ID].data;
        end
        else begin
            assign l2.wr_data_push = 0;
            assign l2.wr_data = 0;
        end
        if (USE_DTAG_INVALIDATIONS) begin
            assign l1_response[L1_DCACHE_ID].inv_addr = l2.inv_addr;
            assign l1_response[L1_DCACHE_ID].inv_valid = l2.inv_valid;
        end
        else begin
            assign l1_response[L1_DCACHE_ID].inv_addr = 0;
            assign l1_response[L1_DCACHE_ID].inv_valid = 0;
        end
    endgenerate

    generate if (USE_DCACHE) begin
            always_comb begin
                l2_requests[L1_DCACHE_ID].addr = l1_request[L1_DCACHE_ID].addr[31:2];
                l2_requests[L1_DCACHE_ID].rnw = l1_request[L1_DCACHE_ID].rnw;
                l2_requests[L1_DCACHE_ID].be = l1_request[L1_DCACHE_ID].be;
                l2_requests[L1_DCACHE_ID].is_amo = l1_request[L1_DCACHE_ID].is_amo;
                l2_requests[L1_DCACHE_ID].amo_type_or_burst_size = l1_request[L1_DCACHE_ID].is_amo ? l1_request[L1_DCACHE_ID].amo : l1_request[L1_DCACHE_ID].size;
                l2_requests[L1_DCACHE_ID].sub_id = L1_DCACHE_ID;
            end
        end
    endgenerate

    generate if (USE_ICACHE) begin
            always_comb begin
                l2_requests[L1_ICACHE_ID].addr = l1_request[L1_ICACHE_ID].addr[31:2];
                l2_requests[L1_ICACHE_ID].rnw = l1_request[L1_ICACHE_ID].rnw;
                l2_requests[L1_ICACHE_ID].be = l1_request[L1_ICACHE_ID].be;
                l2_requests[L1_ICACHE_ID].is_amo = l1_request[L1_ICACHE_ID].is_amo;
                l2_requests[L1_ICACHE_ID].amo_type_or_burst_size = l1_request[L1_ICACHE_ID].size;
                l2_requests[L1_ICACHE_ID].sub_id = L1_ICACHE_ID;
            end
        end
    endgenerate

    generate if (ENABLE_S_MODE) begin
            always_comb begin
                l2_requests[L1_DMMU_ID].addr = l1_request[L1_DMMU_ID].addr[31:2];
                l2_requests[L1_DMMU_ID].rnw = l1_request[L1_DMMU_ID].rnw;
                l2_requests[L1_DMMU_ID].be = l1_request[L1_DMMU_ID].be;
                l2_requests[L1_DMMU_ID].is_amo = l1_request[L1_DMMU_ID].is_amo;
                l2_requests[L1_DMMU_ID].amo_type_or_burst_size = l1_request[L1_DMMU_ID].size;
                l2_requests[L1_DMMU_ID].sub_id = L1_DMMU_ID;

                l2_requests[L1_IMMU_ID].addr = l1_request[L1_IMMU_ID].addr[31:2];
                l2_requests[L1_IMMU_ID].rnw = l1_request[L1_IMMU_ID].rnw;
                l2_requests[L1_IMMU_ID].be = l1_request[L1_IMMU_ID].be;
                l2_requests[L1_IMMU_ID].is_amo = l1_request[L1_IMMU_ID].is_amo;
                l2_requests[L1_IMMU_ID].amo_type_or_burst_size = l1_request[L1_IMMU_ID].size;
                l2_requests[L1_IMMU_ID].sub_id = L1_IMMU_ID;
            end
        end
    endgenerate


    always_comb begin
        l2.addr = l2_requests[L1_CONNECTIONS-1].addr;
        l2.rnw = l2_requests[L1_CONNECTIONS-1].rnw;
        l2.be = l2_requests[L1_CONNECTIONS-1].be;
        l2.is_amo = l2_requests[L1_CONNECTIONS-1].is_amo;
        l2.amo_type_or_burst_size = l2_requests[L1_CONNECTIONS-1].amo_type_or_burst_size;
        l2.sub_id = l2_requests[L1_CONNECTIONS-1].sub_id;
        for (int i = L1_CONNECTIONS-2; i >= 0; i--) begin
            if (requests[i]) begin
		        l2.addr = l2_requests[i].addr;
                l2.rnw = l2_requests[i].rnw;
                l2.be = l2_requests[i].be;
                l2.is_amo = l2_requests[i].is_amo;
                l2.amo_type_or_burst_size = l2_requests[i].amo_type_or_burst_size;
                l2.sub_id = l2_requests[i].sub_id;
			end
        end
    end

    generate
        for (i=0; i <L1_CONNECTIONS; i++) begin
            assign l1_response[i].data = l2.rd_data;
            assign l1_response[i].data_valid = l2.rd_data_valid && (l2.rd_sub_id == i);
        end
    endgenerate

endmodule

