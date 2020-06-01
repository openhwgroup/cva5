/*
 * Copyright © 2019 Eric Matthews,  Lesley Shannon
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

module id_inuse (
        input logic clk,
        input logic rst,
        input logic [4:0] rs1_addr,
        input logic [4:0] rs2_addr,
        input logic [4:0] issued_rd_addr,
        input id_t issue_id,
        input id_t retired_id,
        input logic issued,
        input logic retired,
        output logic rs1_inuse,
        output logic rs2_inuse
        );
    ////////////////////////////////////////////////////
    logic [4:0] rd_addr_list [MAX_INFLIGHT_COUNT-1:0];

    logic [MAX_INFLIGHT_COUNT-1:0] id_inuse;
    logic [MAX_INFLIGHT_COUNT-1:0] id_inuse_new;

    logic [MAX_INFLIGHT_COUNT-1:0] issue_id_one_hot;
    logic [MAX_INFLIGHT_COUNT-1:0] retired_id_one_hot;
    ////////////////////////////////////////////////////
    //Implementation

    always_comb begin
        issue_id_one_hot = 0;
        issue_id_one_hot[issue_id] = issued;

        retired_id_one_hot = 0;
        retired_id_one_hot[retired_id] = retired;

        id_inuse_new = issue_id_one_hot | (id_inuse & ~retired_id_one_hot);
    end

    always_ff @ (posedge clk) begin
        if (rst)
            id_inuse <= '0;
        else
            id_inuse <= id_inuse_new;
    end

    always_ff @ (posedge clk) begin
        if (issued)
            rd_addr_list[issue_id] <= issued_rd_addr;
    end

    always_comb begin
        rs1_inuse = 0;
        rs2_inuse = 0;

        foreach(rd_addr_list[i]) begin
            rs1_inuse |= ({id_inuse[i], rd_addr_list[i]} == {1'b1, rs1_addr});
            rs2_inuse |= ({id_inuse[i], rd_addr_list[i]} == {1'b1, rs2_addr});
        end
    end
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////


    ////////////////////////////////////////////////////
    //Assertions

endmodule




