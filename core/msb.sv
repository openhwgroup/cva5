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
 
module msb
        (
        input logic [31:0] msb_input,
        output logic [4:0] msb
        );

    logic [2:0] sub_msb [3:0];
    logic [3:0] bit_found;

    //Finds MSB for 4x 8-bit segments in parallel
    //Is smaller and faster than checking the full width sequentially (i.e. from 0 to 31)
    always_comb begin
		  for (int i=0; i<4; i=i+1) begin
            bit_found[i] = |msb_input[i*8+:8];
            sub_msb[i] = 0;
            for (int j=1;j<8; j++) begin
                if (msb_input[(i*8)+j])
                    sub_msb[i] = j;
            end
        end

        msb = {2'b0,sub_msb[0]};
        for (int i=1; i<4; i=i+1) begin
            if(bit_found[i]) msb = {i[1:0],sub_msb[i]};
        end
    end
endmodule
