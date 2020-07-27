//Copyright 1986-2019 Xilinx, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Tool Version: Vivado v.2019.2.1 (lin64) Build 2729669 Thu Dec  5 04:48:12 MST 2019
//Date        : Fri Jul 24 11:12:29 2020
//Host        : BefuddledZipper-Desktop.hitronhub.home running 64-bit unknown
//Command     : generate_target design_1_wrapper.bd
//Design      : design_1_wrapper
//Purpose     : IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

module design_1_wrapper
   (sin,
    sout);
  input sin;
  output sout;

  wire sin;
  wire sout;

  design_1 design_1_i
       (.sin(sin),
        .sout(sout));
endmodule
