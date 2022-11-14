
# Set the reference directory for source file relative paths (by default the value is script directory path)
set origin_dir [file dirname [info script]]

# Set the project name
set _xil_proj_name_ "cva5_nexys_wrapper"

set sources_dir $origin_dir/../../../

# Create project
create_project ${_xil_proj_name_} $origin_dir/${_xil_proj_name_} 

# Set the directory path for the new project
set proj_dir [get_property directory [current_project]]


# Set project properties
set obj [current_project]
set_property -name "simulator_language" -value "Mixed" -objects $obj
set_property -name "target_language" -value "Verilog" -objects $obj

# Create 'sources_1' fileset (if not found)
if {[string equal [get_filesets -quiet sources_1] ""]} {
  create_fileset -srcset sources_1
}

#import sources needed for blackbox packaging
import_files -norecurse $sources_dir/examples/nexys/nexys_wrapper.sv
import_files -norecurse $sources_dir/l2_arbiter/l2_external_interfaces.sv
import_files -norecurse $sources_dir/local_memory/local_memory_interface.sv
import_files -norecurse $sources_dir/core/external_interfaces.sv
import_files -norecurse $sources_dir/core/cva5_config.sv
import_files -norecurse $sources_dir/core/riscv_types.sv
import_files -norecurse $sources_dir/core/cva5_types.sv
import_files -norecurse $sources_dir/core/csr_types.sv
import_files -norecurse $sources_dir/l2_arbiter/l2_config_and_types.sv

# Set IP repository paths
set obj [get_filesets sources_1]
set_property "ip_repo_paths" "[file normalize "$origin_dir/${_xil_proj_name_}"]" $obj

# Rebuild user ip_repo's index before adding any source files
update_ip_catalog -rebuild

# Set 'sources_1' fileset properties
set obj [get_filesets sources_1]
set_property -name "top" -value "nexys_wrapper" -objects $obj
set_property -name "top_auto_set" -value "0" -objects $obj
set_property -name "top_file" -value " ${sources_dir}/examples/nexys/nexys_wrapper.sv" -objects $obj


############## Initial IP Packaging 
ipx::package_project -import_files -force -root_dir $proj_dir
update_compile_order -fileset sources_1
ipx::create_xgui_files [ipx::current_core]
ipx::update_checksums [ipx::current_core]
ipx::save_core [ipx::current_core]

# To set the axi interface as aximm and port map all the signals over #

##### Naming
set_property name CVA5 [ipx::current_core]
set_property display_name CVA5_NEXYS7 [ipx::current_core]
set_property description CVA5_NEXYS7 [ipx::current_core]
set_property vendor {} [ipx::current_core]
set_property vendor user [ipx::current_core]

##### Re-Adding of project files
set_property  ip_repo_paths  $sources_dir/${_xil_proj_name_} [current_project]
current_project $_xil_proj_name_
update_ip_catalog
import_files -force -fileset [get_filesets sources_1] $sources_dir/core
import_files -force -fileset [get_filesets sources_1] $sources_dir/l2_arbiter
import_files -force -fileset [get_filesets sources_1] $sources_dir/local_memory
import_files -fileset [get_filesets sources_1] $sources_dir/examples/nexys/l1_to_axi.sv

############## Re-packaging of core
update_compile_order -fileset sources_1
ipx::merge_project_changes files [ipx::current_core]
set_property core_revision 1 [ipx::current_core]
ipx::create_xgui_files [ipx::current_core]
ipx::update_checksums [ipx::current_core]
ipx::save_core [ipx::current_core]
current_project ${_xil_proj_name_} 
set_property "ip_repo_paths" "[file normalize "$origin_dir/${_xil_proj_name_} "]" $obj
update_ip_catalog -rebuild

