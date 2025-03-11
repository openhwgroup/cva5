###############################################################
VERILATOR_DIR=$(CVA5_DIR)/test_benches/verilator

# Sources for verilator
CVA5_HW_SRCS = $(addprefix $(CVA5_DIR)/, $(shell cat $(CVA5_DIR)/tools/compile_order))
CVA5_SIM_SRCS = $(addprefix $(VERILATOR_DIR)/, CVA5Tracer.cc SimMem.cc AXIMem.cc cva5_sim.cc)


#Tracing: Set to True or False
TRACE_ENABLE = True

#Simulation Binary Name
CVA5_SIM_DIR?=$(VERILATOR_DIR)/build
CVA5_SIM?=$(CVA5_SIM_DIR)/cva5-sim


#AXI DDR Parameters
DETERMINISTIC?=0

CFLAGS = -g0 -O3 -std=c++14 -march=native -DDETERMINISTIC=$(DETERMINISTIC)

#Verilator
################################################################################
VERILATOR_LINT_IGNORE= -Wno-LITENDIAN -Wno-SYMRSVDWORD
ifeq ($(TRACE_ENABLE), True)
	VERILATOR_CFLAGS =  --trace-fst --trace-structs --CFLAGS "$(CFLAGS)  -D TRACE_ON"
else
	VERILATOR_CFLAGS =   --CFLAGS  "$(CFLAGS)"
endif

VERILATOR_LINT_IGNORE= -Wno-LITENDIAN -Wno-SYMRSVDWORD


##################################################################################

#cva5_sim included as linter requires top-level to have no interfaces
.PHONY: lint
lint: 
	verilator -cc $(CVA5_HW_SRCS) \
	$(VERILATOR_DIR)/cva5_sim.sv \
	$(CVA5_DIR)/test_benches/sim_stats.sv \
	--top-module cva5_sim \
	--lint-only

.PHONY: lint-full
lint-full:
	verilator -cc $(CVA5_HW_SRCS) \
	$(VERILATOR_DIR)/cva5_sim.sv \
	$(CVA5_DIR)/test_benches/sim_stats.sv \
	--top-module cva5_sim \
	--lint-only -Wall

#Build CVA5 Sim
$(CVA5_SIM): $(CVA5_HW_SRCS) $(CVA5_SIM_SRCS)
	mkdir -p $(CVA5_SIM_DIR)
	verilator --cc --exe --Mdir $(CVA5_SIM_DIR) --assert \
		-o cva5-sim \
		$(VERILATOR_LINT_IGNORE) $(VERILATOR_CFLAGS) \
		$(CVA5_SIM_SRCS) \
		$(CVA5_HW_SRCS) $(CVA5_DIR)/test_benches/verilator/sim_stats.sv $(CVA5_DIR)/test_benches/verilator/cva5_sim.sv --top-module cva5_sim
	$(MAKE) -C $(CVA5_SIM_DIR) -f Vcva5_sim.mk

.PHONY: clean-cva5-sim
clean-cva5-sim:
	rm -rf $(CVA5_SIM_DIR)

