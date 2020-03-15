# Taiga

Taiga is a 32-bit RISC-V processor designed for FPGAs supporting the Multiply/Divide and Atomic extensions (RV32IMA).  The processor is written in SystemVerilog and has been designed to be both highly extensible and highly configurable.

The pipeline has been designed to support parallel, variable-latency execution units and to readily support the inclusion of new execution units.

![Taiga Block Diagram](examples/zedboard/taiga_small.png)


## License

Taiga is licensed under the Apache License, Version 2.0 ( https://www.apache.org/licenses/LICENSE-2.0 )


## Examples
A zedboard configuration is provided under the examples directory along with tools for running stand-alone applications and providing application level simulation of the system.  (See the README in the zedboard directory for details.)


## Publications
E. Matthews, A. Lu, Z. Fang and L. Shannon, "Rethinking Integer Divider Design for FPGA-Based Soft-Processors," 2019 IEEE 27th Annual International Symposium on Field-Programmable Custom Computing Machines (FCCM), San Diego, CA, USA, 2019, pp. 289-297.
doi: [https://doi.org/10.1109/FCCM.2019.00046](https://doi.org/10.1109/FCCM.2019.00046)

E. Matthews, Z. Aguila and L. Shannon, "Evaluating the Performance Efficiency of a Soft-Processor, Variable-Length, Parallel-Execution-Unit Architecture for FPGAs Using the RISC-V ISA," 2018 IEEE 26th Annual International Symposium on Field-Programmable Custom Computing Machines (FCCM), Boulder, CO, 2018, pp. 1-8.
doi: [https://doi.org/10.1109/FCCM.2018.00010](https://doi.org/10.1109/FCCM.2018.00010)

E. Matthews and L. Shannon, "TAIGA: A new RISC-V soft-processor framework enabling high performance CPU architectural features," 2017 27th International Conference on Field Programmable Logic and Applications (FPL), Ghent, Belgium, 2017. [https://doi.org/10.23919/FPL.2017.8056766](https://doi.org/10.23919/FPL.2017.8056766)