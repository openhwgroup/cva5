/*
 * Copyright © 2018 Eric Matthews,  Lesley Shannon
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
import csr_types::*;

module mstatus_priv_reg (
        input logic clk,
        input logic rst,

        input logic exception,
        input logic interrupt,
        input logic mret,
        input logic sret,
        input logic write_msr_m,
        input logic write_msr_s,
        input logic [XLEN-1:0] updated_csr,
        input logic interrupt_delegated,
        input logic exception_delegated,
        output logic [1:0] privilege_level,
        output logic [1:0] next_privilege_level,

        output mstatus_t mstatus,
        output mstatus_t mstatus_smask
        );

    logic [1:0] trap_return_privilege_level, exception_privilege_level, interrupt_privilege_level;
    mstatus_t mstatus_exception, mstatus_return, mstatus_rst, mstatus_new;
    mstatus_t mstatus_mmask, mstatus_mask;


    assign trap_return_privilege_level = mret ? mstatus.mpp : {1'b0,mstatus.spp}; //sret --> {1'b0,mstatus.spp}
    assign exception_privilege_level = exception_delegated ? SUPERVISOR_PRIV : MACHINE_PRIV;
    assign interrupt_privilege_level = interrupt_delegated ? SUPERVISOR_PRIV : MACHINE_PRIV;

    always_comb begin
        unique if(mret | sret)
            next_privilege_level = trap_return_privilege_level;
        else if (interrupt)
            next_privilege_level = interrupt_privilege_level;
        else if (exception)
            next_privilege_level = exception_privilege_level;
        else
            next_privilege_level = privilege_level;
    end

    //Current privilege level
    always_ff @(posedge clk) begin
        if (rst)
            privilege_level <= MACHINE_PRIV;
        else
            privilege_level <= next_privilege_level;
    end

    always_comb begin
        mstatus_exception = mstatus;
        unique case (next_privilege_level)
            SUPERVISOR_PRIV: begin
                mstatus_exception.spie = (privilege_level == SUPERVISOR_PRIV) ? mstatus.sie : mstatus.uie;
                mstatus_exception.sie = 0;
                mstatus_exception.spp = privilege_level[0]; //one if from supervisor-mode, zero if from user-mode
            end
            default: begin
                mstatus_exception.mpie = (privilege_level == MACHINE_PRIV) ? mstatus.mie : ((privilege_level == SUPERVISOR_PRIV) ? mstatus.sie : mstatus.uie);
                mstatus_exception.mie = 0;
                mstatus_exception.mpp = privilege_level; //machine,supervisor or user
            end
        endcase
    end

    //return from trap
    always_comb begin
        mstatus_return = mstatus;
        unique if (sret) begin
            mstatus_return.sie = mstatus_return.spie;
            mstatus_return.spie = 1;
            mstatus_return.spp = 0;
        end else if (mret) begin
            mstatus_return.mie = mstatus.mpie;
            mstatus_return.mpie = 1;
            mstatus_return.mpp = USER_PRIV;
        end
    end

    //CSR write masks:
    assign mstatus_mmask = '{default:0, mprv:1, mxr:1, sum:1, mpp:'1, spp:1, mpie:1, spie:1, mie:1, sie:1};
    assign mstatus_smask  = '{default:0, mxr:1, sum:1, spp:1, spie:1, sie:1};
    assign mstatus_mask = write_msr_m ? mstatus_mmask : mstatus_smask;
    /////////////////

    always_comb begin
        unique if (write_msr_m | write_msr_s)
            mstatus_new = updated_csr & mstatus_mask;
        else if (interrupt | exception)
            mstatus_new = mstatus_exception;
        else if (mret | sret)
            mstatus_new = mstatus_return;
        else
            mstatus_new = mstatus;
    end

    assign mstatus_rst = '{default:0, mpp:MACHINE_PRIV};
    always_ff @(posedge clk) begin
        if (rst)
            mstatus <= mstatus_rst;
        else
            mstatus <= mstatus_new;
    end

endmodule


