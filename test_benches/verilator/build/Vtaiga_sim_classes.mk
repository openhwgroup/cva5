# Verilated -*- Makefile -*-
# DESCRIPTION: Verilator output: Make include file with class lists
#
# This file lists generated Verilated files, for including in higher level makefiles.
# See Vtaiga_sim.mk for the caller.

### Switches...
# C11 constructs required?  0/1 (always on now)
VM_C11 = 1
# Coverage output mode?  0/1 (from --coverage)
VM_COVERAGE = 0
# Parallel builds?  0/1 (from --output-split)
VM_PARALLEL_BUILDS = 1
# Threaded output mode?  0/1/N threads (from --threads)
VM_THREADS = 0
# Tracing output mode?  0/1 (from --trace/--trace-fst)
VM_TRACE = 0
# Tracing output mode in VCD format?  0/1 (from --trace)
VM_TRACE_VCD = 0
# Tracing output mode in FST format?  0/1 (from --trace-fst)
VM_TRACE_FST = 0

### Object file lists...
# Generated module classes, fast-path, compile with highest optimization
VM_CLASSES_FAST += \
	Vtaiga_sim \
	Vtaiga_sim___024root__DepSet_haf24fdd0__0 \
	Vtaiga_sim___024root__DepSet_haf24fdd0__1 \
	Vtaiga_sim___024root__DepSet_haf24fdd0__2 \
	Vtaiga_sim___024root__DepSet_hc0ab74a6__0 \
	Vtaiga_sim_clz_tree__DepSet_he43dc3c6__0 \
	Vtaiga_sim_lfsr__W4__DepSet_h9aa69f04__0 \

# Generated module classes, non-fast-path, compile with low/medium optimization
VM_CLASSES_SLOW += \
	Vtaiga_sim__ConstPool_0 \
	Vtaiga_sim___024root__Slow \
	Vtaiga_sim___024root__DepSet_haf24fdd0__0__Slow \
	Vtaiga_sim___024root__DepSet_haf24fdd0__1__Slow \
	Vtaiga_sim___024root__DepSet_hc0ab74a6__0__Slow \
	Vtaiga_sim___024unit__Slow \
	Vtaiga_sim___024unit__DepSet_h2aad04a1__0__Slow \
	Vtaiga_sim_l2_memory_interface__Slow \
	Vtaiga_sim_l2_memory_interface__DepSet_h157bd95f__0__Slow \
	Vtaiga_sim_l2_arbitration_interface__Slow \
	Vtaiga_sim_l2_arbitration_interface__DepSet_h526f6300__0__Slow \
	Vtaiga_sim_l2_requester_interface__Slow \
	Vtaiga_sim_l2_requester_interface__DepSet_h86e282ce__0__Slow \
	Vtaiga_sim_branch_predictor_interface__Slow \
	Vtaiga_sim_branch_predictor_interface__DepSet_hb44c7630__0__Slow \
	Vtaiga_sim_ras_interface__Slow \
	Vtaiga_sim_ras_interface__DepSet_he821f2c0__0__Slow \
	Vtaiga_sim_exception_interface__Slow \
	Vtaiga_sim_exception_interface__DepSet_h540032cb__0__Slow \
	Vtaiga_sim_tlb_interface__Slow \
	Vtaiga_sim_tlb_interface__DepSet_h9632d003__0__Slow \
	Vtaiga_sim_register_file_issue_interface__pi1__Slow \
	Vtaiga_sim_register_file_issue_interface__pi1__DepSet_h15db40fa__0__Slow \
	Vtaiga_sim_renamer_interface__N2__Slow \
	Vtaiga_sim_renamer_interface__N2__DepSet_hc1750c21__0__Slow \
	Vtaiga_sim_load_store_queue_interface__Slow \
	Vtaiga_sim_load_store_queue_interface__DepSet_h6e6b6a24__0__Slow \
	Vtaiga_sim_fp_renamer_interface__Slow \
	Vtaiga_sim_fp_renamer_interface__DepSet_heddaa626__0__Slow \
	Vtaiga_sim_fp_register_file_issue_interface__Slow \
	Vtaiga_sim_fp_register_file_issue_interface__DepSet_h3e7b6293__0__Slow \
	Vtaiga_sim_axi_interface__Slow \
	Vtaiga_sim_axi_interface__DepSet_hda38b023__0__Slow \
	Vtaiga_sim_fetch_sub_unit_interface__pi5__Slow \
	Vtaiga_sim_fetch_sub_unit_interface__pi5__DepSet_h584d0d41__0__Slow \
	Vtaiga_sim_ls_sub_unit_interface__pi11__Slow \
	Vtaiga_sim_ls_sub_unit_interface__pi11__DepSet_h8917c96a__0__Slow \
	Vtaiga_sim_ls_sub_unit_interface__pi12__Slow \
	Vtaiga_sim_ls_sub_unit_interface__pi12__DepSet_he78f5e8b__0__Slow \
	Vtaiga_sim_unit_issue_interface__Slow \
	Vtaiga_sim_unit_issue_interface__DepSet_h6839aae5__0__Slow \
	Vtaiga_sim_unit_writeback_interface__Slow \
	Vtaiga_sim_unit_writeback_interface__DepSet_hc6e89073__0__Slow \
	Vtaiga_sim_fp_unit_writeback_interface__Slow \
	Vtaiga_sim_fp_unit_writeback_interface__DepSet_h9dc29b36__0__Slow \
	Vtaiga_sim_clz_tree__Slow \
	Vtaiga_sim_clz_tree__DepSet_hfbb27690__0__Slow \
	Vtaiga_sim_fifo_interface__D2b__Slow \
	Vtaiga_sim_fifo_interface__D2b__DepSet_h38fb3fb8__0__Slow \
	Vtaiga_sim_fifo_interface__D20__Slow \
	Vtaiga_sim_fifo_interface__D20__DepSet_h101b13c1__0__Slow \
	Vtaiga_sim_fifo_interface__D1e__Slow \
	Vtaiga_sim_fifo_interface__D1e__DepSet_h65c56eea__0__Slow \
	Vtaiga_sim_fifo_interface__D22__Slow \
	Vtaiga_sim_fifo_interface__D22__DepSet_hb016e6fb__0__Slow \
	Vtaiga_sim_fifo_interface__D2c__Slow \
	Vtaiga_sim_fifo_interface__D2c__DepSet_h354d1d74__0__Slow \
	Vtaiga_sim_fifo_interface__D7__Slow \
	Vtaiga_sim_fifo_interface__D7__DepSet_h14bedb50__0__Slow \
	Vtaiga_sim_fifo_interface__D23__Slow \
	Vtaiga_sim_fifo_interface__D23__DepSet_hb79b8cdc__0__Slow \
	Vtaiga_sim_fifo_interface__D5__Slow \
	Vtaiga_sim_fifo_interface__D5__DepSet_hdc7c1ed2__0__Slow \
	Vtaiga_sim_fifo_interface__D3__Slow \
	Vtaiga_sim_fifo_interface__D3__DepSet_hcebebfc8__0__Slow \
	Vtaiga_sim_fifo_interface__D6__Slow \
	Vtaiga_sim_fifo_interface__D6__DepSet_h9c6872e7__0__Slow \
	Vtaiga_sim_fifo_interface__D12__Slow \
	Vtaiga_sim_fifo_interface__D12__DepSet_h60d46ebc__0__Slow \
	Vtaiga_sim_fifo_interface__Db__Slow \
	Vtaiga_sim_fifo_interface__Db__DepSet_hc8bb9294__0__Slow \
	Vtaiga_sim_fifo_interface__D52__Slow \
	Vtaiga_sim_fifo_interface__D52__DepSet_h0b5165ad__0__Slow \
	Vtaiga_sim_fifo_interface__D4__Slow \
	Vtaiga_sim_fifo_interface__D4__DepSet_h8679caec__0__Slow \
	Vtaiga_sim_fifo_interface__D110__Slow \
	Vtaiga_sim_fifo_interface__D110__DepSet_h79728537__0__Slow \
	Vtaiga_sim_fifo_interface__D54__Slow \
	Vtaiga_sim_fifo_interface__D54__DepSet_h16841cf5__0__Slow \
	Vtaiga_sim_unsigned_sqrt_interface__D38__Slow \
	Vtaiga_sim_unsigned_sqrt_interface__D38__DepSet_h81d26671__0__Slow \
	Vtaiga_sim_fifo_interface__Db0__Slow \
	Vtaiga_sim_fifo_interface__Db0__DepSet_h6a6ad9ab__0__Slow \
	Vtaiga_sim_lfsr__W4__Slow \
	Vtaiga_sim_lfsr__W4__DepSet_had29d352__0__Slow \
	Vtaiga_sim_unsigned_division_interface__Slow \
	Vtaiga_sim_unsigned_division_interface__DepSet_h51c0f92b__0__Slow \
	Vtaiga_sim_unsigned_division_interface__pi16__Slow \
	Vtaiga_sim_unsigned_division_interface__pi16__DepSet_h8a39f908__0__Slow \

# Generated support classes, fast-path, compile with highest optimization
VM_SUPPORT_FAST += \

# Generated support classes, non-fast-path, compile with low/medium optimization
VM_SUPPORT_SLOW += \
	Vtaiga_sim__Syms \

# Global classes, need linked once per executable, fast-path, compile with highest optimization
VM_GLOBAL_FAST += \
	verilated \

# Global classes, need linked once per executable, non-fast-path, compile with low/medium optimization
VM_GLOBAL_SLOW += \


# Verilated -*- Makefile -*-
