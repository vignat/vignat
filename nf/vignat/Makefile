# Pick your verification-time stub!
# DPDK, DRIVER, or HARDWARE
STUB_KIND = HARDWARE

# Pick your compile-time flags! (i.e. not for verification)
CFLAGS += -O3
#CFLAGS += -O0 -g -rdynamic -DENABLE_LOG -Wfatal-errors



### Abandon all hope, ye who enter here! ###



# allow the use of extglob in paths
SHELL = /bin/bash -O extglob -c

# DPDK stuff
include $(RTE_SDK)/mk/rte.vars.mk

# binary name
APP = nat

# sources
SRCS-y := nat_forward_vignat.c ../nf_main.c ../lib/nat_config.c \
          ../lib/nf_time.c ../lib/nf_util.c \
          ../lib/flow.c ../lib/flow-log.c flowmanager.c flowtable.c \
          ../lib/expirator.c \
          ../lib/containers/double-chain.c ../lib/containers/double-chain-impl.c \
          ../lib/containers/map-impl.c ../lib/containers/double-map.c \
          ../lib/containers/vector.c ../lib/containers/map.c

# gcc flags
CFLAGS += -std=gnu99 -I../..

# disable warnings triggered by DPDK
CFLAGS += -Wno-implicit-function-declaration
CFLAGS += -Wno-nested-externs

# DPDK stuff
include $(RTE_SDK)/mk/rte.extapp.mk



### VeriFast verification ###
verifast:
	verifast -I . -I .. -allow_assume -shared \
		../lib/assumptions_stubs.c \
		../lib/flow.c \
		../lib/containers/double-chain-impl.c \
		../lib/containers/double-chain.c \
		../lib/containers/map-impl.c \
		../lib/containers/double-map.c \
		../lib/containers/batcher.c \
		../lib/coherence.c \
		../lib/expirator.c \
		../lib/containers/array-bat-verifast.c \
		../lib/containers/array-rq-verifast.c \
		../lib/containers/array-u16-verifast.c \
		../lib/containers/array-lcc-verifast.c \
		abstract-state-verify-lemmas.c



### KLEE verification ###

# Basic flags: only compile, emit debug code, in LLVM format, with checks for overflows
#              (but not unsigned overflows - they're not UB and DPDK depends on them)
VERIF_FLAGS := -c -g -emit-llvm -fsanitize=signed-integer-overflow

# Basic includes: VigNAT, NF files, and KLEE
VERIF_INCLUDES := -I . -I .. -I $(KLEE_INCLUDE)

# Defines. TODO remove _GNU_SOURCE from here, #define it in files
VERIF_DEFS := -D_GNU_SOURCE -DKLEE_VERIFICATION -DVIGOR_STUB_$(STUB_KIND)

# Basic files
# VigNAT
VERIF_FILES := nat_forward_vignat.c flowtable.c flowmanager.c ../lib/nat_config.c ../lib/flow.c ../lib/flow-log.c
# The NF base
VERIF_FILES += ../nf_main.c ../lib/nf_util.c
# NAT-specific stubs
VERIF_FILES += loop-stub.c
# NF stubs
VERIF_FILES += ../lib/stubs/containers/double-chain-stub.c ../lib/stubs/containers/double-map-stub.c ../lib/stubs/containers/expirator-stub.c
# Environment stubs
VERIF_FILES += ../lib/stubs/externals/*.c ../lib/stubs/core_stub.c ../lib/stubs/time_stub.c

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
# Platform-independent and Linux-specific EAL
VERIF_DPDK_FILES += $(RTE_SDK)/lib/librte_eal/common/*.c $(RTE_SDK)/lib/librte_eal/linuxapp/eal/*.c
# Other libraries, except acl and distributor which use CPU intrinsics (there is a generic version of distributor, but we don't need it),
# and power has been broken for a while: http://dpdk.org/ml/archives/dev/2016-February/033152.html
VERIF_DPDK_FILES += $(RTE_SDK)/lib/!(librte_acl|librte_distributor|librte_power)/*.c
# Stacks for mempool
VERIF_DPDK_FILES += $(RTE_SDK)/drivers/mempool/stack/*.c
# Virtual devices support (for stub drivers)
VERIF_DPDK_FILES += $(RTE_SDK)/drivers/bus/vdev/*.c
# PCI driver support (for ixgbe driver)
VERIF_DPDK_FILES += $(RTE_SDK)/drivers/bus/pci/*.c $(RTE_SDK)/drivers/bus/pci/linux/*.c
# ixgbe driver (except bypass, SSE and ARM NEON stuff)
VERIF_DPDK_FILES += $(RTE_SDK)/drivers/net/ixgbe/!(ixgbe_bypass|ixgbe_82599_bypass|ixgbe_rxtx_vec_sse|ixgbe_rxtx_vec_neon).c $(RTE_SDK)/drivers/net/ixgbe/base/*.c


ifeq ($(STUB_KIND), DPDK)
# Use DPDK stub headers
VERIF_INCLUDES += -I ../lib/stubs/dpdk
else ifeq ($(STUB_KIND), DRIVER)
# Use DPDK stuff
VERIF_INCLUDES += $(VERIF_DPDK_INCLUDES)
VERIF_DEFS += $(VERIF_DPDK_DEFS)
VERIF_FILES += $(VERIF_DPDK_FILES)
# And the stub drivers
VERIF_FILES += ../lib/stubs/driver_stub.c
else ifeq ($(STUB_KIND), HARDWARE)
# Use DPDK stuff
VERIF_INCLUDES += $(VERIF_DPDK_INCLUDES)
VERIF_DEFS += $(VERIF_DPDK_DEFS)
VERIF_FILES += $(VERIF_DPDK_FILES)
# And the stub hardware
VERIF_FILES += ../lib/stubs/hardware_stub.c
else
$(error Please use a proper value for STUB_KIND)
endif

verify:
	# Cleanup in case previous build failed after generating bc files
	rm -f *.bc

	clang $(VERIF_INCLUDES) $(VERIF_DEFS) $(VERIF_FILES) $(VERIF_FLAGS)

	# Link
	llvm-link -o veri.bc *.bc

	# if something takes longer than expected, try --max-solver-time=3 --debug-report-symbdex
        # can't use -optimize because does inlining and removes functions that we need to trace or use for aliases
	/usr/bin/time -v `# print time/mem stats` \
	klee -libc=uclibc -no-externals -dump-call-traces -dump-call-trace-prefixes -solver-backend=z3 -exit-on-error -max-memory=750000 --max-solver-time=3 --debug-report-symbdex \
		veri.bc \
		--no-shconf `# don't mmap the config` \
		-- \
		`# TODO make those parameters symbolic` \
		--lan-dev 0 \
		--wan 1 \
		--expire 10 \
		--starting-port 0 \
		--max-flows 65536 \
		--extip 0.0.0.0 \
		--eth-dest 0,01:23:45:67:89:00 \
		--eth-dest 1,01:23:45:67:89:01
	rm -f *.bc
