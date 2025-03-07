# Set project name and origin directory
set origin_dir [file dirname [info script]]
set _xil_proj_name_ "axi_clint_top_IP"

# Create Vivado project
create_project ${_xil_proj_name_} $origin_dir/${_xil_proj_name_} -part xcvu9p-flga2104-2L-e -force

# Set board and project properties
set obj [current_project]
set_property -name "board_part" -value "xilinx.com:vcu118:part0:2.4" -objects $obj
set_property -name "default_lib" -value "xil_defaultlib" -objects $obj
set_property -name "ip_cache_permissions" -value "read write" -objects $obj
set_property -name "ip_output_repo" -value "$origin_dir/${_xil_proj_name_}.cache/ip" -objects $obj
set_property -name "sim.ip.auto_export_scripts" -value "1" -objects $obj
set_property -name "simulator_language" -value "Mixed" -objects $obj
set_property -name "target_language" -value "Verilog" -objects $obj

# Create 'sources_1' fileset
if {[string equal [get_filesets -quiet sources_1] ""]} {
  create_fileset -srcset sources_1
}

# Import the wishbone_plic_top module
import_files -norecurse $origin_dir/plic.sv -force
import_files -norecurse $origin_dir/plic_cmptree.sv -force
import_files -norecurse $origin_dir/plic_gateway.sv -force
import_files -norecurse $origin_dir/plic_wrapper.sv -force

# Set top module
set obj [get_filesets sources_1]
set_property -name "top" -value "plic_wrapper" -objects $obj

# Set IP repository paths
set obj [get_filesets sources_1]
set_property "ip_repo_paths" "[file normalize "$origin_dir"]" $obj

# Update IP catalog
update_ip_catalog -rebuild



# create_ip -name ila -vendor xilinx.com -library ip -version 6.2 -module_name ila_clint
# set_property -dict [list CONFIG.C_PROBE3_WIDTH {32} CONFIG.C_PROBE1_WIDTH {64} CONFIG.C_PROBE0_WIDTH {64} CONFIG.C_NUM_OF_PROBES {4}] [get_ips ila_clint]
# generate_target {instantiation_template} [get_files /media/CVA5_PLIC/cva5/axi_plic_top_IP/axi_plic_top_IP.srcs/sources_1/ip/ila_clint/ila_clint.xci]



############## Initial IP Packaging########################################
ipx::package_project -import_files -force -root_dir $origin_dir
update_compile_order -fileset sources_1


# ipx::add_subcore xilinx.com:ip:ila:6.2 [ipx::get_file_groups xilinx_anylanguagesynthesis -of_objects [ipx::current_core]]


ipx::add_bus_interface s_axi [ipx::current_core]
set_property name s_axi [ipx::get_bus_interfaces S_AXI -of_objects [ipx::current_core]]
ipx::add_bus_parameter NUM_READ_OUTSTANDING [ipx::get_bus_interfaces s_axi -of_objects [ipx::current_core]]
ipx::add_bus_parameter NUM_WRITE_OUTSTANDING [ipx::get_bus_interfaces s_axi -of_objects [ipx::current_core]]


puts "INFO: IP package ${_xil_proj_name_} created successfully."

exit