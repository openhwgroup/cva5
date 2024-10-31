/*
 * Copyright © 2024 Chris Keilbart, Mohammad Shahidzadeh
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
 *             Mohammad Shahidzadeh <mohammad_shahidzadeh_asadi@sfu.ca>
 */

module clint

    #(
        parameter int unsigned NUM_CORES = 1
    ) (
        input logic clk,
        input logic rst,

        input logic write_mtime,
        input logic write_mtimecmp,
        input logic write_msip,
        input logic write_upper, //Else lower; mtime and mtimecmp only
        input logic [(NUM_CORES == 1) ? 0 : ($clog2(NUM_CORES)-1) : 0] write_msip_core,
        input logic [(NUM_CORES == 1) ? 0 : ($clog2(NUM_CORES)-1) : 0] write_mtimecmp_core,
        input logic[31:0] write_data,

        output logic[1:0][31:0] mtime,
        output logic[NUM_CORES-1:0][1:0][31:0] mtimecmp,
        output logic[NUM_CORES-1:0] msip,
        output logic[NUM_CORES-1:0] mtip
    );

    ////////////////////////////////////////////////////
    //Core Local INTerrupt unit (CLINT)
    //Implements mtime, mtimecmp, mtip, and msip from the RISC-V privileged specification
    //mtime increments at a constant frequency
    //mtip is set when mtime >= mtimecmp
    //mtimecmp and msip are registers
    logic[63:0] mtime_p_1;
    assign mtime_p_1 = {mtime[1], mtime[0]} + 1;

    always_ff @(posedge clk) begin
        if (rst) begin
            mtime <= '0;
            mtimecmp <= '1; //Reset to max to prevent interrupts
            msip <= '0;
        end
        else begin
            for (int i = 0; i < NUM_CORES; i++)
                mtip[i] <= {mtime[1], mtime[0]} >= {mtimecmp[i][1], mtimecmp[i][0]};
            
            mtime[1] <= write_mtime & write_upper ? write_data : mtime_p_1[63:32];
            mtime[0] <= write_mtime & ~write_upper ? write_data : mtime_p_1[31:0];
            
            for (int i = 0; i < NUM_CORES; i++) begin     
                mtimecmp[i][1] <= write_mtimecmp & write_upper & i == int'(write_mtimecmp_core) ? write_data : mtimecmp[i][1];           
                mtimecmp[i][0] <= write_mtimecmp & ~write_upper & i == int'(write_mtimecmp_core) ? write_data : mtimecmp[i][0];
            end

            if (write_msip)
                msip[write_msip_core] <= write_data[0]; //LSB
        end
    end

endmodule
