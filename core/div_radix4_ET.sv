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
 *             Alec Lu <alec_lu@sfu.ca>
 */


module div_radix4_ET
        #(
            parameter C_WIDTH = 32
        )(
            input logic clk,
            input logic rst,
            input logic start,
            input logic ack,
            input logic [C_WIDTH-1:0] A,
            input logic [C_WIDTH-1:0] B,
            output logic [C_WIDTH-1:0] Q,
            output logic [C_WIDTH-1:0] R,
            output logic complete
        );

    logic terminate;
    logic terminate_early;
    logic [C_WIDTH/2-1:0] shift_count;

    logic [C_WIDTH+1:0] PR;
    logic [2:0] new_PR_sign;
    logic [C_WIDTH+2:0] new_PR_1;
    logic [C_WIDTH+2:0] new_PR_2;
    logic [C_WIDTH+2:0] new_PR_3;
    logic [C_WIDTH+1:0] B_1;
    logic [C_WIDTH+1:0] B_2;
    logic [C_WIDTH+1:0] B_3;

    //implementation
    ////////////////////////////////////////////////////
    assign new_PR_1 = {1'b0, PR} - {1'b0, B_1};
    assign new_PR_2 = {1'b0, PR} - {1'b0, B_2};
    assign new_PR_3 = {1'b0, PR} - {1'b0, B_3};
    assign new_PR_sign = {new_PR_3[C_WIDTH+2], new_PR_2[C_WIDTH+2], new_PR_1[C_WIDTH+2]};

    //Shift reg for
    always_ff @ (posedge clk) begin
        shift_count <= {shift_count[14:0], start & ~terminate_early};
    end

    assign terminate_early = B > A;

    always_ff @ (posedge clk) begin
        if (start) begin
            if (terminate_early) begin
                PR <= {A, 2'b00};
                Q <= '0;
            end
            else begin
                PR <= {{(C_WIDTH-1){1'b0}}, A[C_WIDTH-1:C_WIDTH-2]};
                Q <= {A[C_WIDTH-3:0], 2'b00};
            end
            B_1 <= {2'b0, B};           //1xB
            B_2 <= {1'b0, B, 1'b0};     //2xB
            B_3 <= {1'b0, B, 1'b0} + B; //3xB
        end
        else if (~terminate) begin
            casex (new_PR_sign)
                3'b111 : begin
                    PR <= {PR[C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-2]};
                    Q <= {Q[C_WIDTH-3:0], 2'b00};
                end
                3'b110 : begin
                    PR <= {new_PR_1[C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-2]};
                    Q <= {Q[C_WIDTH-3:0], 2'b01};
                end
                3'b100 : begin
                    PR <= {new_PR_2[C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-2]};
                    Q <= {Q[C_WIDTH-3:0], 2'b10};
                end
                3'b000 : begin
                    PR <= {new_PR_3[C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-2]};
                    Q <= {Q[C_WIDTH-3:0], 2'b11};
                end
                default begin
                    PR <= 'x;
                    Q <= 'x;
                end
            endcase
        end
    end

    assign R = PR[C_WIDTH+1:2];

    always_ff @ (posedge clk) begin
        if (rst)
            terminate <= 0;
        else begin
            if (start)
                if (terminate_early) begin
                    terminate <= 1;
                end else begin
                    terminate <= 0;
                end
            if (shift_count[15])
                terminate <= 1;
        end
    end

    always_ff @ (posedge clk) begin
        if (rst)
            complete <= 0;
        else begin
            if (ack)
                complete <= 0;
            else if ((~start & (shift_count[15])) | (start & terminate_early))
                complete <= 1;
        end
    end

endmodule
