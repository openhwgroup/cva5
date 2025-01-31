puts "This script will create a system project for CVA5 in the current folder to run a demo application from block memory on the Nexys A7-100T"
puts "You should install the board support files from https://github.com/Digilent/vivado-boards before running this script"

# Create the project
create_project -force -part xc7a100tcsg324-1 CVA5BD ./vivado/CVA5BD
set_property board_part digilentinc.com:nexys-a7-100t:part0:1.3 [current_project]
set_property ip_repo_paths ./vivado/ip_repo [current_project]
update_ip_catalog

# Block diagram
create_bd_design "soc"
# UART
create_bd_cell -type ip -vlnv xilinx.com:ip:axi_uartlite:2.0 axi_uartlite_0
apply_board_connection -board_interface "usb_uart" -ip_intf "axi_uartlite_0/UART" -diagram "soc"
# Reset
create_bd_cell -type ip -vlnv xilinx.com:ip:proc_sys_reset:5.0 proc_sys_reset_0
apply_board_connection -board_interface "reset" -ip_intf "proc_sys_reset_0/ext_reset" -diagram "soc" 
# Clock
create_bd_cell -type ip -vlnv xilinx.com:ip:clk_wiz:6.0 clk_wiz_0
# Connect to clock on board
apply_bd_automation -rule xilinx.com:bd_rule:board -config { Board_Interface {sys_clock ( System Clock ) } Manual_Source {Auto}}  [get_bd_pins clk_wiz_0/clk_in1]
# Connect to reset on board via inverter
apply_bd_automation -rule xilinx.com:bd_rule:board -config { Board_Interface {reset ( Reset ) } Manual_Source {New External Port (ACTIVE_HIGH)}}  [get_bd_pins clk_wiz_0/reset]
# Processor
create_bd_cell -type ip -vlnv xilinx.com:user:cva5_top:1.0 cva5_top_0
# Connect processor to UART via interconnect
apply_bd_automation -rule xilinx.com:bd_rule:axi4 -config { Clk_master {Auto} Clk_slave {Auto} Clk_xbar {Auto} Master {/cva5_top_0/m_axi} Slave {/axi_uartlite_0/S_AXI} ddr_seg {Auto} intc_ip {New AXI Interconnect} master_apm {0}}  [get_bd_intf_pins axi_uartlite_0/S_AXI]
# Set address space
set_property offset 0x60000000 [get_bd_addr_segs {cva5_top_0/m_axi/SEG_axi_uartlite_0_Reg}]

regenerate_bd_layout

make_wrapper -files [get_files ./vivado/CVA5BD/CVA5BD.srcs/sources_1/bd/soc/soc.bd] -top
add_files ./vivado/CVA5BD/CVA5BD.gen/sources_1/bd/soc/hdl/soc_wrapper.v
update_compile_order -fileset sources_1
