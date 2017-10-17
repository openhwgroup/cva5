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

module normdiv
        #(
        parameter C_WIDTH = 32
        )
        (
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

    logic running;
    logic terminate;

    logic [C_WIDTH:0] new_PR;
    logic [C_WIDTH:0] PR;

    logic [$clog2(C_WIDTH):0] count;

    assign  new_PR = {1'b0, PR} - {1'b0, B};

    always_ff @ (posedge clk) begin
        if (start) begin
            count <= C_WIDTH;
            PR <= {{(C_WIDTH-2){1'b0}}, A[C_WIDTH-1]};
            Q <= {A[C_WIDTH-2:0], 1'b0};
        end
        else if (~terminate) begin
            if (new_PR[C_WIDTH]) begin
                PR <= {PR[C_WIDTH-1:0], Q[C_WIDTH-1]};
                Q <= {Q[C_WIDTH-2:0], 1'b0};
            end
            else begin
                PR <= {new_PR[C_WIDTH-1:0], Q[C_WIDTH-1]};
                Q <= {Q[C_WIDTH-2:0], 1'b1};
            end
            count <= count - 1;
        end
    end

    assign R = PR[C_WIDTH:1];

    assign terminate = (count == 0);

    always_ff @ (posedge clk) begin
        if (rst) begin
            running <= 0;
            complete <= 0;
        end
        else begin
            if (start) begin
                running <= 1;
                complete <= 0;
            end
            else if (running & terminate) begin
                running <= 0;
                complete <= 1;
            end
            else if (ack) begin
                running <= 0;
                complete <= 0;
            end
        end
    end

endmodule
