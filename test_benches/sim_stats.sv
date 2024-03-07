/*
 * Copyright © 2022 Eric Matthews,  Lesley Shannon
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

module sim_stats

    import cva5_config::*;
    import cva5_types::*;

    #(
        parameter NUM_OF_STATS = 32,
        parameter NUM_INSTRUCTION_MIX_STATS = 5
    )
    (
        input logic clk,
        input logic rst,
        input logic start_collection,
        input logic end_collection,
        input logic stats [NUM_OF_STATS],
        input logic [NUM_INSTRUCTION_MIX_STATS-1:0] instruction_mix_stats [RETIRE_PORTS],
        input logic [LOG2_RETIRE_PORTS:0] retire_count
    );
    int log_file;
    logic en;

    logic [63:0] instructions_retired;
    logic [63:0] cycle_count;
    logic [63:0] stat_count [NUM_OF_STATS];
    logic [63:0] instruction_mix_stat_count [NUM_INSTRUCTION_MIX_STATS-1:0];
    logic [$clog2(RETIRE_PORTS):0] instruction_mix_inc [NUM_INSTRUCTION_MIX_STATS-1:0];

    function real to_percent (input logic [63:0] a, input logic [63:0] b);
        to_percent = 100.0 * real'(a)/real'(a + b);
    endfunction

    function void print_stats ();
        $display("Fetch---------------------------------------------------------");
        $display("Early Branch Correction : %-d", stat_count[FETCH_EARLY_BR_CORRECTION_STAT]);
        $display("Sub Unit Stall : %-d", stat_count[FETCH_SUB_UNIT_STALL_STAT]);
        $display("No ID available : %-d", stat_count[FETCH_ID_STALL_STAT]);
        $display("Instruction Cache");
        $display("  Hits : %-d (%.2f%%)", stat_count[FETCH_IC_HIT_STAT], to_percent(stat_count[FETCH_IC_HIT_STAT], stat_count[FETCH_IC_MISS_STAT]));
        $display("  Misses : %-d", stat_count[FETCH_IC_MISS_STAT]);
        $display("  Arbiter stall : %-d", stat_count[FETCH_IC_ARB_STALL_STAT]);
        $display("Branch Predictor");
        $display("  Branches");
        $display("    Correct : %-d (%.2f%%)", stat_count[FETCH_BP_BR_CORRECT_STAT], to_percent(stat_count[FETCH_BP_BR_CORRECT_STAT], stat_count[FETCH_BP_BR_MISPREDICT_STAT]));
        $display("    Mispredict : %-d", stat_count[FETCH_BP_BR_MISPREDICT_STAT]);
        $display("  Returns (RAS)");
        $display("    Correct : %-d (%.2f%%)", stat_count[FETCH_BP_RAS_CORRECT_STAT], to_percent(stat_count[FETCH_BP_RAS_CORRECT_STAT], stat_count[FETCH_BP_RAS_MISPREDICT_STAT]));
        $display("    Mispredict : %-d", stat_count[FETCH_BP_RAS_MISPREDICT_STAT]);

        $display("Issue---------------------------------------------------------");
        $display("Stall Sources");
        $display("  No Instruction : %-d (%.2f%%)", stat_count[ISSUE_NO_INSTRUCTION_STAT], to_percent(stat_count[ISSUE_NO_INSTRUCTION_STAT], stat_count[ISSUE_UNIT_BUSY_STAT]+stat_count[ISSUE_OPERANDS_NOT_READY_STAT]+stat_count[ISSUE_HOLD_STAT]));
        $display("    Max IDs Issued : %-d", stat_count[ISSUE_NO_ID_STAT]);
        $display("    Flush : %-d", stat_count[ISSUE_FLUSH_STAT]);
        $display("  Unit Busy : %-d (%.2f%%)", stat_count[ISSUE_UNIT_BUSY_STAT], to_percent(stat_count[ISSUE_UNIT_BUSY_STAT], stat_count[ISSUE_NO_INSTRUCTION_STAT]+stat_count[ISSUE_OPERANDS_NOT_READY_STAT]+stat_count[ISSUE_HOLD_STAT]));
        $display("  Operands Not Ready : %-d (%.2f%%)", stat_count[ISSUE_OPERANDS_NOT_READY_STAT], to_percent(stat_count[ISSUE_OPERANDS_NOT_READY_STAT], stat_count[ISSUE_UNIT_BUSY_STAT]+stat_count[ISSUE_NO_INSTRUCTION_STAT]+stat_count[ISSUE_HOLD_STAT]));
        $display("  Hold : %-d (%.2f%%)", stat_count[ISSUE_HOLD_STAT], to_percent(stat_count[ISSUE_HOLD_STAT], stat_count[ISSUE_UNIT_BUSY_STAT]+stat_count[ISSUE_NO_INSTRUCTION_STAT]+stat_count[ISSUE_OPERANDS_NOT_READY_STAT]));
        $display("  Multi-Source : %-d", stat_count[ISSUE_MULTI_SOURCE_STAT]);
        $display("Operand Stall Waiting On");
        $display("  Load : %-d (%.2f%%)", stat_count[ISSUE_OPERAND_STALL_ON_LOAD_STAT], to_percent(stat_count[ISSUE_OPERAND_STALL_ON_LOAD_STAT], stat_count[ISSUE_OPERANDS_NOT_READY_STAT] - stat_count[ISSUE_OPERAND_STALL_ON_LOAD_STAT]));
        $display("  Multiply : %-d (%.2f%%)", stat_count[ISSUE_OPERAND_STALL_ON_MULTIPLY_STAT], to_percent(stat_count[ISSUE_OPERAND_STALL_ON_MULTIPLY_STAT], stat_count[ISSUE_OPERANDS_NOT_READY_STAT] - stat_count[ISSUE_OPERAND_STALL_ON_MULTIPLY_STAT]));
        $display("  Divide : %-d (%.2f%%)", stat_count[ISSUE_OPERAND_STALL_ON_DIVIDE_STAT], to_percent(stat_count[ISSUE_OPERAND_STALL_ON_DIVIDE_STAT], stat_count[ISSUE_OPERANDS_NOT_READY_STAT] - stat_count[ISSUE_OPERAND_STALL_ON_DIVIDE_STAT]));
        $display("Operands Stall (Branch) : %-d", stat_count[ISSUE_OPERAND_STALL_FOR_BRANCH_STAT]);
        $display("Store with Forwarded Data : %-d", stat_count[ISSUE_STORE_WITH_FORWARDED_DATA_STAT]);
        $display("Divider Result Reuse : %-d", stat_count[ISSUE_DIVIDER_RESULT_REUSE_STAT]);

        $display("Load-Store Unit-----------------------------------------------");
        $display("Load Blocked by Store : %-d", stat_count[LSU_LOAD_BLOCKED_BY_STORE_STAT]);
        $display("Sub Unit Stall : %-d", stat_count[LSU_SUB_UNIT_STALL_STAT]);
        $display("Data Cache");
        $display("  Hits : %-d (%.2f%%)", stat_count[LSU_DC_HIT_STAT], to_percent(stat_count[LSU_DC_HIT_STAT], stat_count[LSU_DC_MISS_STAT]));
        $display("  Misses : %-d", stat_count[LSU_DC_MISS_STAT]);
        $display("  Arbiter stall : %-d", stat_count[LSU_DC_ARB_STALL_STAT]);

        $display("Retire--------------------------------------------------------");
        $display("Instructions Retired : %-d", instructions_retired);
        $display("Runtime (cycles) : %-d", cycle_count);
        $display("IPC : %-f", real'(instructions_retired)/real'(cycle_count));
        $display("Instruction Mix");
        $display("  Basic ALU : %-d (%.2f%%)", instruction_mix_stat_count[ALU_STAT], to_percent(instruction_mix_stat_count[ALU_STAT],instructions_retired - instruction_mix_stat_count[ALU_STAT]));
        $display("  Branch or Jump : %-d (%.2f%%)", instruction_mix_stat_count[BR_STAT], to_percent(instruction_mix_stat_count[BR_STAT],instructions_retired - instruction_mix_stat_count[BR_STAT]));
        $display("  Multiply : %-d (%.2f%%)", instruction_mix_stat_count[MUL_STAT], to_percent(instruction_mix_stat_count[MUL_STAT],instructions_retired - instruction_mix_stat_count[MUL_STAT]));
        $display("  Divide : %-d (%.2f%%)", instruction_mix_stat_count[DIV_STAT], to_percent(instruction_mix_stat_count[DIV_STAT],instructions_retired - instruction_mix_stat_count[DIV_STAT]));
        $display("  Load : %-d (%.2f%%)", instruction_mix_stat_count[LOAD_STAT], to_percent(instruction_mix_stat_count[LOAD_STAT],instructions_retired - instruction_mix_stat_count[LOAD_STAT]));
        $display("  Store : %-d (%.2f%%)", instruction_mix_stat_count[STORE_STAT], to_percent(instruction_mix_stat_count[STORE_STAT],instructions_retired - instruction_mix_stat_count[STORE_STAT]));
        $display("  FPU : %-d (%.2f%%)", instruction_mix_stat_count[FPU_STAT], to_percent(instruction_mix_stat_count[FPU_STAT],instructions_retired - instruction_mix_stat_count[FPU_STAT]));
        $display("  Misc : %-d (%.2f%%)", instruction_mix_stat_count[MISC_STAT], to_percent(instruction_mix_stat_count[MISC_STAT],instructions_retired - instruction_mix_stat_count[MISC_STAT]));
        $display("");
    endfunction

    import "DPI-C" function string cva5_csv_log_file_name();
    function void print_stats_csv ();
        stats_t stat_enum;
        instruction_mix_stats_t instruction_mix_stat_enum;
        if (log_file != 0) begin
            $fdisplay(log_file, "Instructions Retired,%-d", instructions_retired);
            $fdisplay(log_file, "Runtime (cycles),%-d", cycle_count);
            $fdisplay(log_file, "IPC,%-f", real'(instructions_retired)/real'(cycle_count));
            foreach(stat_count[i]) begin
                stat_enum = stats_t'(i);
                $fdisplay(log_file, "%s,%-d", stat_enum.name(), stat_count[i]);
            end
            foreach(instruction_mix_stat_count[i]) begin
                instruction_mix_stat_enum = instruction_mix_stats_t'(i);
                $fdisplay(log_file, "%s,%-d", instruction_mix_stat_enum.name(), instruction_mix_stat_count[i]);
            end
            $fclose(log_file);
        end
    endfunction

    ////////////////////////////////////////////////////
    //Implementation
    initial begin
        if (cva5_csv_log_file_name() != "")
            log_file = $fopen(cva5_csv_log_file_name(), "w");
    end


    always_ff @ (posedge clk) begin
        if (end_collection) begin
            print_stats();
            print_stats_csv();
        end
    end

    always_ff @ (posedge clk) begin
        if (rst)
            en <= 0;
        else
            en <= (en & ~end_collection) | start_collection;
    end

    always_comb begin
        instruction_mix_inc = '{default: 0};
        for (int i = 0; i < RETIRE_PORTS; i++) begin
            for (int j = 0; j < NUM_INSTRUCTION_MIX_STATS; j++) begin
                instruction_mix_inc[j] += ($clog2(RETIRE_PORTS)+1)'(instruction_mix_stats[i][j]);
            end
        end
    end

    always_ff @ (posedge clk) begin
        if (rst) begin
            instructions_retired <= 0;
            cycle_count <= 0;
            foreach (stat_count[i])
                stat_count[i] <= 0;
            foreach (instruction_mix_stat_count[i])
                instruction_mix_stat_count[i] <=0;
        end
        if (en) begin
            instructions_retired <= instructions_retired + 64'(retire_count);
            cycle_count <= cycle_count + 1;
            foreach (stat_count[i])
                stat_count[i] <= stat_count[i] + 64'(stats[i]);
            foreach (instruction_mix_stat_count[i])
                instruction_mix_stat_count[i] <= instruction_mix_stat_count[i] + 64'(instruction_mix_inc[i]);
        end
    end

endmodule
