Creating a Project for the Zedboard
================


    1. Select the zedboard as your board in Vivado and import standard board constraints
    2. Add Taiga core and l2 arbiter sources to the project
    3. Add the taiga_wrapper.sv from the zedboard directory
    4. Add the Xilinx specific components which are generated through tcl scripts. From the Tcl Console run:
        source <path to>/arm.tcl
        source <path to/>system_peripherals.tcl

System Configuration
-----
For this example system, the AXI bus interface is enabled for Taiga, and a UART is connected to the bus.  The memory interface is through the L2 arbiter to a High Performance Port on the ARM.

![Taiga Block Diagram](system.png)



Simulation
-----------
For application level simulation we have provided a top level system wrapper: taiga_tb.sv, a waveform conifuration file and a python script to convert riscv binaries into a input usable for the simulation.
 
To simulate the system add all the sources in the simulation folder.  Set taiga_tb.sv as the top level entity and update the following two lines with paths to your benchmark simulation file and your uart output log file.  For testing purposes we have included a dhrystone.riscv.sim_init file that can be used to verify that the design has been correctly configured.

    `define  MEMORY_FILE  "<path to sim_init file>"
    `define  UART_LOG  "<output log>"

Additionally, add the waveform config file to your project which includes many of the key control signals within Taiga and allows for the observation of program execution.  The testbench waveform is configured to show the dissasembly of the program as it executes to aid in debugging and unsderstanding of instruction flow within Taiga.

![Sample Simulator Output](simulator_output_example.png)

The simulation will run for a set amout of time units which can be modified by changing the 1200000 value below.

    initial begin
        simulator_clk = 0;
        interrupt = '0;
        simulator_resetn = 0;
                
        simulation_mem.load_program(`MEMORY_FILE, RESET_VEC);
        
        output_file = $fopen(`UART_LOG, "w");
        if (output_file == 0) begin
            $error ("couldn't open log file");
            $finish;
        end
        do_reset();

        #1200000;
        $fclose(output_file);
        $finish;
    end

Upon reaching finish, the simulator will flush the buffer to the output file and the uart log can be checked.  If the simulation is stopped early, the output_file will not show all/any writes to the UART.


Building Software
-----------
To build stand-alone software you will need to build the risc-v gcc toolchain and riscv-tests:
[https://github.com/riscv/riscv-tools](https://github.com/riscv/riscv-tools)


Build the tools for a RV32IMA configuration.  To build new stand-alone applications the benchmarks in the riscv-tests can be used as a starting point.

### Changes Required
In order to build your own applications you will need to make a few small modifications to the setup in the riscv-tests/benchmarks directory.

In the riscv-tests/benchmarks/Makefile, make sure XLEN is set to 32, and add -DHOST_DEBUG=0 to the RISCV_GCC_OPTS.

In riscv-tests/benchmarks/common/crt.S the default stack size is 128KB which would well exceed a reasonable BRAM configuration.  To change the stack size change the the STKSHIFT define.  For 2KBs, set the value to 11.

For UART support you will need to modify the riscv-tests/benchmarks/common/syscalls.c file, specifically, the putchar function.  Replace this function with one that sends a character to the UART.

### Creating the simulation and BRAM init files
To create the inputs for simulation, use the taiga_binary_converter.py (from the tools directory) on the resulting binaries to create inputs for simulation and BRAM initialization for hardware.

The taiga_binary_converter.py script requires the following inputs:

    python3 taiga_binary_converter.py <riscv-gcc-prefix> <base addr> <ram size in bytes> <input binary> <output BRAM init file> <output Simulation init file>

Here is an example set of inputs for the script:

    python3 taiga_binary_converter.py riscv32-unknown-elf- 0x80000000 65536 dhrystone.riscv  dhrystone.riscv.hw_init  dhrystone.riscv.sim_init

Building the core on the Zedboard
-----
Tested on Vivado 2018.3
### Building Taiga and Local Memory IP Cores
In Vivado's TCL Console, change its directory to within the cloned Taiga repository:

    cd <path to Taiga repo location>/Taiga
    
Build the Taiga  IP Package by calling:
    
    source taiga_wrapper_IP.tcl
    
Build the Local Memory Package by calling:

    source local_memory_IP.tcl

These commands will create separate Vivado projects, check if the packaging was successful. In the "Package IP" tab, navigate to the "Review and Package", a succesfully built IP core with have a Re-Package IP button at the bottom.

Both a Successful and failed build will create IP core folders(taiga_wrapper_IP and local_memory_IP) within the Taiga directory.

Note: If for some reason, it neccesary to run the scripts again, always delete the the IP core folder of the core that will be rebuilt, as Vivado is unable to overwrite these files otherwise.


### Adding Taiga and Local Memory IP Cores to the project
In either the existing Vivado project or a new Vivado project configured to run on a zedBoard, open the "IP Catalog".

Add the IPs, by right-clicking on the Catalog Window, select "Add Repository..." and direct it to the Taiga Repository.

There should now be a User Repository that contains the cores:

local_mem_v1_0 and taiga_wrapper_xilinx_v1_0


### Creating the Hardware Block Diagram and configuring IP Cores:
Create a new Block Design by selecting "Create Block Design" in Vivado's Flow Navigator.
Add the following IP cores:

    1. taiga_wrapper_xilinx_v1_0
    2. local_mem_v1_0
    3. ZYNQ7 Processing System
    4. Processor System Reset
    4. AXI Interconnect (NOT AXI Smartconnect)
    5. AXI UART16550

Configure the local_mem IP to use a Preloaded File, by double-cliking on the core and setting "Use Preload File" to 1 and copy the file path to the hw_init file provided.
Leave "Ram Size" to 64.

Configure the AXI Interconnect to use "Maximize Performance" as its "Optimization Strategy". This requires the interconnect to **not** be a 1-to-1 interconnect even if functionally it only connects the Taiga core to the UART. This can be done by setting either the Number of Slave or Master Interfaces to 2.

This was done because Vivado would optimized neccesarry signals away that would cause the interconnect to fail to transfer requests from the Taiga to the UART. This is the same reason as to why the AXI Smartconnect is not used.

Configure the ZYNQ7 Processing System to output an FCLK_CLK of 100Mhz. This can be set in the IP's "Clock Configuration" under "PL Fabric Clocks:. Ensure there is at least 1 FCLK enabled and its Requested Frequency is 100Mhz.


[unfinished]


