/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 * 
 * This Source Code Form is "Incompatible With Secondary Licenses", as
 * defined by the Mozilla Public License, v. 2.0.
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
