/*
 * Copyright © 2020 Eric Matthews,  Lesley Shannon
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

module instruction_metadata

    import taiga_config::*;
    import taiga_types::*;

    (
        input logic clk,
        input logic rst,

        //Fetch
        input id_t pc_id,
        input logic [31:0] if_pc,
        input logic pc_id_assigned,

        input id_t fetch_id,
        input logic fetch_complete,
        input logic [31:0] fetch_instruction,

        //Decode ID
        input id_t decode_id,
        output logic [31:0] decode_pc,
        output logic [31:0] decode_instruction,

        //Issue stage
        input issue_packet_t issue,
        input logic instruction_issued,
        output id_t rs_id [REGFILE_READ_PORTS],
        output logic rs_inuse [REGFILE_READ_PORTS],

        //Branch Predictor
        input branch_metadata_t branch_metadata_if,
        input id_t branch_id,
        output branch_metadata_t branch_metadata_ex,

        //Writeback/Register File
        input id_t ids_retiring [COMMIT_PORTS],
        output logic [4:0] retired_rd_addr [COMMIT_PORTS],
        output id_t id_for_rd [COMMIT_PORTS],
        //Exception
        input id_t exception_id,
        output logic [31:0] exception_pc

    );
    //////////////////////////////////////////
    logic [31:0] pc_table [MAX_IDS];
    logic [31:0] instruction_table [MAX_IDS];
    logic [$bits(branch_metadata_t)-1:0] branch_metadata_table [MAX_IDS];
    logic [31:0] rd_table [MAX_IDS];

    //Writes to register file
    id_t rd_to_id_table [32];
    ////////////////////////////////////////////////////
    //Implementation

    //pc table
    always_ff @ (posedge clk) begin
        if (pc_id_assigned)
            pc_table[pc_id] <= if_pc;
    end

    //branch metadata table
    always_ff @ (posedge clk) begin
        if (pc_id_assigned)
            branch_metadata_table[pc_id] <= branch_metadata_if;
    end

    //instruction table
    always_ff @ (posedge clk) begin
        if (fetch_complete)
            instruction_table[fetch_id] <= fetch_instruction;
    end

    ////////////////////////////////////////////////////
    //Operand inuse determination
    initial rd_to_id_table = '{default: 0};
    always_ff @ (posedge clk) begin
        if (instruction_issued & issue.uses_rd)//tracks most recently issued instruction that writes to the register file
            rd_to_id_table[issue.rd_addr] <= issue.id;
    end

    ////////////////////////////////////////////////////
    //Outputs

    //Decode
    assign decode_pc = pc_table[decode_id];
    assign decode_instruction = instruction_table[decode_id];

    //Branch Predictor
    assign branch_metadata_ex = branch_metadata_table[branch_id];

    //Issue
    always_comb begin
        for (int i = 0; i < REGFILE_READ_PORTS; i++) begin
            rs_id[i] = rd_to_id_table[issue.rs_addr[i]];
            rs_inuse[i] = (issue.rs_addr[i] == instruction_table[rs_id[i]][11:7]);//11:7 is rd_addr
        end
    end

    //Writeback support
    always_comb begin
        for (int i = 0; i < COMMIT_PORTS; i++) begin
            retired_rd_addr[i] = instruction_table[ids_retiring[i]][11:7];
            id_for_rd[i] = rd_to_id_table[retired_rd_addr[i]];
        end
    end

    //Exception Support
     generate if (ENABLE_M_MODE) begin
         assign exception_pc = pc_table[exception_id];
     end endgenerate

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
