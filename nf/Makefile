# Skeleton Makefile for Vigor NFs
# Variables that should be defined by inheriting Makefiles:
# - APP := <binary name>
# - NF_FILES := <NF files for both runtime and verif-time>
# - NF_VERIF_FILES := <verif-time only NF files>
# - NF_VERIF_ARGS := <arguments to pass to the NF at verif-time>

# -----------------------------------------------------------------------

# get current dir
# see https://stackoverflow.com/a/8080530
SELF_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

# DPDK stuff
include $(RTE_SDK)/mk/rte.vars.mk

# allow the use of extglob in paths
SHELL = /bin/bash -O extglob -c

# NF base source
SRCS-y := $(SELF_DIR)/nf_main.c \
          $(SELF_DIR)/lib/nf_time.c \
          $(SELF_DIR)/lib/nf_util.c \
          $(SELF_DIR)/lib/expirator.c \
          $(SELF_DIR)/lib/containers/double-chain.c $(SELF_DIR)/lib/containers/double-chain-impl.c \
          $(SELF_DIR)/lib/containers/map.c $(SELF_DIR)/lib/containers/map-impl.c \
          $(SELF_DIR)/lib/containers/double-map.c \
          $(SELF_DIR)/lib/containers/vector.c
# NF specific source
SRCS-y += $(NF_FILES)

# compiler flags
CFLAGS += -I $(SELF_DIR)
CFLAGS += -std=gnu99
CFLAGS += -O3
#CFLAGS += -O0 -g -rdynamic -DENABLE_LOG -Wfatal-errors

# disable warnings triggered by DPDK
#CFLAGS += -Wno-implicit-function-declaration
#CFLAGS += -Wno-nested-externs

# DPDK stuff
include $(RTE_SDK)/mk/rte.extapp.mk

### VeriFast verification ###
# we use DPDK stubs in there (e.g. rte_config.h)
verifast:
	verifast -I $(SELF_DIR) -I $(SELF_DIR)/lib/stubs/dpdk -allow_assume -shared \
		$(SELF_DIR)/lib/assumptions_stubs.c \
		$(SELF_DIR)/lib/flow.c \
		$(SELF_DIR)/lib/containers/double-chain-impl.c \
		$(SELF_DIR)/lib/containers/double-chain.c \
		$(SELF_DIR)/lib/containers/map-impl.c \
		$(SELF_DIR)/lib/containers/double-map.c \
		$(SELF_DIR)/lib/containers/vector.c \
		$(SELF_DIR)/lib/coherence.c \
		$(SELF_DIR)/lib/expirator.c \
		$(SELF_DIR)/lib/abstract-state-verify-lemmas.c



### KLEE verification ###

# Basic flags: only compile, emit debug code, in LLVM format, with checks for overflows
#              (but not unsigned overflows - they're not UB and DPDK depends on them)
VERIF_FLAGS := -c -g -emit-llvm -fsanitize=signed-integer-overflow

# Basic includes: NF root and KLEE
VERIF_INCLUDES := -I $(SELF_DIR) -I $(KLEE_INCLUDE)
# ...and the DPDK cmdline library
VERIF_INCLUDES += -I $(RTE_SDK)/lib/librte_cmdline

# Defines. TODO remove _GNU_SOURCE from here, #define it in files
VERIF_DEFS := -D_GNU_SOURCE -DKLEE_VERIFICATION

# Basic files
# NF base
VERIF_FILES := $(SELF_DIR)/nf_main.c $(SELF_DIR)/lib/nf_util.c
# Specific NF
VERIF_FILES += $(NF_FILES)
# NF base stubs
VERIF_FILES += ../lib/stubs/containers/map-stub.c ../lib/stubs/containers/double-map-stub.c \
               ../lib/stubs/containers/double-chain-stub.c \
               ../lib/stubs/containers/vector-stub.c \
               ../lib/stubs/containers/expirator-stub.c
# Specific NF stubs
VERIF_FILES += $(NF_VERIF_FILES)
# Environment stubs
VERIF_FILES += ../lib/stubs/externals/*.c ../lib/stubs/core_stub.c ../lib/stubs/time_stub.c
# DPDK cmdline parsing library, always included, we don't want/need to stub it
VERIF_FILES += $(RTE_SDK)/lib/librte_cmdline/*.c
# ...and the string function it uses
VERIF_FILES += $(RTE_SDK)/lib/librte_eal/common/eal_common_string_fns.c

# Defines for DPDK
# CPUFLAGS is set to a sentinel value; usually it's passed from the DPDK build system
VERIF_DPDK_DEFS := -DRTE_COMPILE_TIME_CPUFLAGS=424242

# Includes for DPDK
# We need librte_eal/common because eal_private.h is in there, required by eal_thread.c...
# We need bus/pci because the linuxapp PCI stuff requires a private.h file in there...
# bus/vdev and net/ixgbe are for stub drivers (which are vdevs) and hardware (the ixgbe driver) respectively
VERIF_DPDK_INCLUDES := -I $(RTE_SDK)/$(RTE_TARGET)/include \
			-I $(RTE_SDK)/lib/librte_eal/common \
			-I $(RTE_SDK)/drivers/bus/vdev \
			-I $(RTE_SDK)/drivers/bus/pci \
			-I $(RTE_SDK)/drivers/net/ixgbe
# And then some special DPDK includes: builtin_stubs for built-ins DPDK uses, and rte_config which many DPDK files use without including
VERIF_DPDK_INCLUDES += --include=lib/stubs/builtin_stub.h --include=rte_config.h

# Files for DPDK
# Low-level stubs for specific functions
VERIF_DPDK_FILES := ../lib/stubs/dpdk_low_level_stub.c
# Replacement for the mempool containr
VERIF_DPDK_FILES += ../lib/stubs/dpdk_mempool_singleton.c
# Platform-independent and Linux-specific EAL
VERIF_DPDK_FILES += $(RTE_SDK)/lib/librte_eal/common/*.c $(RTE_SDK)/lib/librte_eal/linuxapp/eal/*.c
# Other libraries, except acl and distributor which use CPU intrinsics (there is a generic version of distributor, but we don't need it),
# and power has been broken for a while: http://dpdk.org/ml/archives/dev/2016-February/033152.html
VERIF_DPDK_FILES += $(RTE_SDK)/lib/!(librte_acl|librte_distributor|librte_power)/*.c
# Virtual devices support (for stub drivers)
VERIF_DPDK_FILES += $(RTE_SDK)/drivers/bus/vdev/*.c
# PCI driver support (for ixgbe driver)
VERIF_DPDK_FILES += $(RTE_SDK)/drivers/bus/pci/*.c $(RTE_SDK)/drivers/bus/pci/linux/*.c
# ixgbe driver (except bypass, SSE and ARM NEON stuff)
VERIF_DPDK_FILES += $(RTE_SDK)/drivers/net/ixgbe/!(ixgbe_bypass|ixgbe_82599_bypass|ixgbe_rxtx_vec_sse|ixgbe_rxtx_vec_neon).c $(RTE_SDK)/drivers/net/ixgbe/base/*.c

# Commands
# Cleanup
CLEAN_COMMAND := rm -f *.bc
# Compilation
COMPILE_COMMAND := clang
# Linking
LINK_COMMAND := llvm-link -o nf.bc *.bc
# KLEE verification
# if something takes longer than expected, try --max-solver-time=3 --debug-report-symbdex
VERIF_COMMAND := /usr/bin/time -v \
                 klee -libc=uclibc -no-externals -dump-call-traces -dump-call-trace-prefixes -solver-backend=z3 -exit-on-error -max-memory=750000
# NF args for the verification
NF_VERIF_BASE_ARGS := nf.bc --no-shconf --


verify-dpdk:
	$(CLEAN_COMMAND)
	# Use DPDK stub headers
	$(COMPILE_COMMAND) $(VERIF_DEFS) -DVIGOR_STUB_DPDK $(VERIF_INCLUDES) -I $(SELF_DIR)/lib/stubs/dpdk $(VERIF_FILES) $(VERIF_FLAGS)
	$(LINK_COMMAND)
	$(VERIF_COMMAND) $(NF_VERIF_BASE_ARGS) $(NF_VERIF_ARGS)
	$(CLEAN_COMMAND)

verify-driver:
	$(CLEAN_COMMAND)
	# Use DPDK stuff + stub driver
	$(COMPILE_COMMAND) $(VERIF_DEFS) $(VERIF_DPDK_DEFS) -DVIGOR_STUB_DRIVER $(VERIF_INCLUDES) $(VERIF_DPDK_INCLUDES) $(VERIF_FILES) $(VERIF_DPDK_FILES) $(SELF_DIR)/lib/stubs/driver_stub.c $(VERIF_FLAGS)
	$(LINK_COMMAND)
	$(VERIF_COMMAND) $(NF_VERIF_BASE_ARGS) $(NF_VERIF_ARGS)
	$(CLEAN_COMMAND)

verify-hardware:
	$(CLEAN_COMMAND)
	# Use DPDK stuff + stub hardware
	$(COMPILE_COMMAND) $(VERIF_DEFS) $(VERIF_DPDK_DEFS) -DVIGOR_STUB_HARDWARE $(VERIF_INCLUDES) $(VERIF_DPDK_INCLUDES) $(VERIF_FILES) $(VERIF_DPDK_FILES) $(SELF_DIR)/lib/stubs/hardware_stub.c $(VERIF_FLAGS)
	$(LINK_COMMAND)
	$(VERIF_COMMAND) $(NF_VERIF_BASE_ARGS) $(NF_VERIF_ARGS)
	$(CLEAN_COMMAND)
