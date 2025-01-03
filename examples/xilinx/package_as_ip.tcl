puts "This script will create a project for CVA5 in the current folder and package it as an IP"

# Create the project
create_project -force -part xc7a100tcsg324-1 CVA5IP ./vivado/CVA5IP
add_files -force {core examples/xilinx examples/sw}
set_property top cva5_top [current_fileset]
update_compile_order -fileset sources_1

# Now package as IP using intermediate project
ipx::package_project -root_dir ./vivado/ip_repo -vendor xilinx.com -library user -taxonomy /UserIP -import_files -set_current false -force
ipx::unload_core ./vivado/ip_repo/component.xml
ipx::edit_ip_in_project -upgrade true -name tmp_edit_project -directory ./vivado/ip_repo ./vivado/ip_repo/component.xml
ipx::update_source_project_archive -component [ipx::current_core]
ipx::create_xgui_files [ipx::current_core]
ipx::update_checksums [ipx::current_core]
ipx::check_integrity [ipx::current_core]
ipx::save_core [ipx::current_core]
ipx::move_temp_component_back -component [ipx::current_core]
close_project -delete
close_project
