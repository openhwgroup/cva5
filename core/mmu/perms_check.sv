/*
 * Copyright © 2024 Liam Feng, Chris Keilbart, Eric Matthews
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
 *             Liam Feng <lfa32@sfu.ca>
 *             Chris Keilbart <ckeilbar@sfu.ca>
 *             Eric Matthews <ematthew@sfu.ca>
 */

module perms_check

    import csr_types::*;

    (
        input pte_perms_t pte_perms,

        input logic rnw, //LS type
        input logic execute, //Fetch
        input logic mxr, //Make eXecutable Readable
        input logic sum, //permit Supervisor User Memory access
        input privilege_t privilege, //Effective operatinf privilege

        output logic valid
    );

    logic access_valid;
    logic privilege_valid;

    //Access and permission checks
    //A and D bits are software managed; this implementation corresponds to the Svade extension
    assign access_valid =
        (execute & pte_perms.x & pte_perms.a) | //fetch
        (rnw & (pte_perms.r | (pte_perms.x & mxr)) & pte_perms.a) | //load
        ((~rnw & ~execute) & pte_perms.w & pte_perms.a & pte_perms.d); //store

    assign privilege_valid = 
        (privilege == MACHINE_PRIVILEGE) |
        ((privilege == SUPERVISOR_PRIVILEGE) & (~pte_perms.u | (pte_perms.u & sum))) |
        ((privilege == USER_PRIVILEGE) & pte_perms.u);
    
    assign valid = access_valid & privilege_valid;
    
endmodule
