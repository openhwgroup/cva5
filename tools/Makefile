.PHONY: lint verilator_stack_test verilator_taiga_test verilator_taiga_compliance

TAIGA_DIR=..
VERILATOR_DIR=$(TAIGA_DIR)/test_benches/verilator

TAIGA_CORE_SV=$(wildcard $(TAIGA_DIR)/core/*.sv)
TAIGA_L2_SV=$(wildcard $(TAIGA_DIR)/l2_arbiter/*.sv)
TAIGA_LOCAL_MEM_SV=$(wildcard $(TAIGA_DIR)/local_memory/*.sv)

TAIGA_SRCS = $(shell cat taiga_compile_order)

VERILATOR_LINT_IGNORE= -Wno-UNOPTFLAT -Wno-WIDTH -Wno-WIDTHCONCAT -Wno-LITENDIAN -Wno-SYMRSVDWORD -Wno-CASEINCOMPLETE -Wno-CASEX
VERILATOR_CFLAGS =  -CFLAGS "-g0 -O2"

BENCHMARK_MEM_INIT=/home/ematthew/Research/RISCV/software/taiga-benchmarks/dhrystone.riscv.hw_init

lint: 
	verilator -cc $(TAIGA_SRCS) \
	--top-module ver_top \
	--lint-only
	
verilator_stack_test:
	mkdir -p $@
	cp $(VERILATOR_DIR)/id_stack_sim.cc $@/
	verilator -cc -Wno-WIDTH --trace --exe  --Mdir $@ ../core/id_stack.sv id_stack_sim.cc 
	$(MAKE) -C  $@ -f Vid_stack.mk
	./$@/Vid_stack
	
verilator_taiga_test:
	mkdir -p $@
	cp $(VERILATOR_DIR)/taiga_full_sim.cc $@/
	verilator -cc -Wno-WIDTH --trace --exe --Mdir $@ $(VERILATOR_LINT_IGNORE) $(VERILATOR_CFLAGS) $(TAIGA_SRCS) ../test_benches/verilator/ver_top.sv --top-module ver_top  taiga_full_sim.cc \
	-GMEMORY_FILE=\"$(BENCHMARK_MEM_INIT)\"
	$(MAKE) -C  $@ -f Vver_top.mk
	./$@/Vver_top
	
verilator_taiga_compliance: $(VERILATOR_DIR)/taiga_local_mem_compliance.cc $(TAIGA_SRCS)
	mkdir -p $@
	cp $(VERILATOR_DIR)/taiga_local_mem_compliance.cc $@/
	verilator -cc -Wno-WIDTH --exe --Mdir $@ $(VERILATOR_LINT_IGNORE) $(VERILATOR_CFLAGS) $(TAIGA_SRCS) ../test_benches/verilator/taiga_local_mem_compliance.sv --top-module taiga_local_mem_compliance  taiga_local_mem_compliance.cc \
	-GMEMORY_FILE=\"$(COMPLIANCE_BENCHAMRK)\"
	$(MAKE) -C  $@ -f Vtaiga_local_mem_compliance.mk
	./$@/Vtaiga_local_mem_compliance $(LOG_FILE_NAME) $(SIG_FILE_NAME)
	
	
