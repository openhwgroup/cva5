module placer_randomizer # (
        parameter logic [7:0] PLACER_SEED = 8'h2B
        )
        (
        input logic clk,
        input logic [7:0] samples,
        output logic result
        );

    always_ff @(posedge clk) begin
        result <= |(samples & PLACER_SEED);
    end

endmodule


