.PHONY: lint verilator_taiga_dhrystone verilator_taiga_benchmarks verilator_taiga_compliance verilator_taiga_coremark

MAKEFILE_DIR=$(pwd)
TAIGA_DIR=..

RISCV_PREFIX   ?= riscv32-newlib-elf-


#Verilator parameters
###############################################################
VERILATOR_DIR=$(TAIGA_DIR)/test_benches/verilator

TAIGA_SRCS = $(shell cat taiga_compile_order)

VERILATOR_LINT_IGNORE= -Wno-UNOPTFLAT -Wno-WIDTH -Wno-WIDTHCONCAT -Wno-LITENDIAN -Wno-SYMRSVDWORD -Wno-CASEINCOMPLETE -Wno-CASEX
VERILATOR_CFLAGS =  -CFLAGS "-g0 -Os -march=native -pipe -flto -Wl,-flto" -LDFLAGS "-flto"

AR="gcc-ar"
RANLIB="gcc-ranlib"
export AR
export RANLIB
###############################################################


#Benchmark parameters
#Assumes binaries are in the BENCHMARK_DIR
###############################################################
BENCHMARK_DIR=/home/ematthew/Research/RISCV/software/taiga-benchmarks/
BENCHMARKS = \
 dhrystone \
 prime \
 rand \
 sqrt \
 micro \
 rsa \
 aes \
 fft \
 qsort \
###############################################################


#Binary to Verilog HW init file
###############################################################
ELF_TO_HW_INIT ?= python3 taiga_binary_converter.py $(RISCV_PREFIX) 0x80000000 131072
###############################################################


COREMARK_DIR=/home/ematthew/Research/RISCV/software/coremark


define verilator_local_mem_test
	mkdir -p $@
	cp $(VERILATOR_DIR)/taiga_local_mem.cc $@/
	verilator -cc -Wno-WIDTH --exe --Mdir $@ $(VERILATOR_LINT_IGNORE) $(VERILATOR_CFLAGS) $(TAIGA_SRCS) \
		 ../test_benches/verilator/taiga_local_mem.sv --top-module taiga_local_mem  taiga_local_mem.cc \
		-GMEMORY_FILE=$1
	$(MAKE) -C  $@ -f Vtaiga_local_mem.mk AR="gcc-ar" RANLIB="gcc-ranlib"
	time ./$@/Vtaiga_local_mem $2 $3
endef

lint: 
	verilator -cc $(TAIGA_SRCS) \
	../test_benches/verilator/taiga_local_mem.sv \
	--top-module taiga_local_mem \
	--lint-only
		
verilator_taiga_dhrystone:
	$(call verilator_local_mem_test,\"$(BENCHMARK_DIR)dhrystone.riscv.hw_init\", "$@/dhrystone.log", "/dev/null")
	
verilator_taiga_benchmarks:
	$(foreach BENCHMARK,$(BENCHMARKS), \
		$(call verilator_local_mem_test,\"$(BENCHMARK_DIR)$(BENCHMARK).riscv.hw_init\", $@/$(BENCHMARK).log, "/dev/null") \
	)

#Called by compliance makefile
verilator_taiga_compliance:
	$(call verilator_local_mem_test,\"$(COMPLIANCE_BENCHAMRK)\", $(LOG_FILE_NAME), $(SIG_FILE_NAME))
	
verilator_taiga_coremark:
	$(MAKE) -C  $(COREMARK_DIR) compile PORT_DIR=taiga-sim ITERATIONS=5000
	cd $(MAKEFILE_DIR);
	$(ELF_TO_HW_INIT) $(COREMARK_DIR)/coremark.bin coremark.hw_init coremark.sim_init
	$(call verilator_local_mem_test,\"coremark.hw_init\", "coremark.log", "coremark.sig")
	
clean:
	rm -rf ./verilator_taiga_dhrystone
	rm -rf ./verilator_taiga_benchmarks
	rm -rf ./verilator_taiga_compliance
	rm -rf ./verilator_taiga_coremark
	
