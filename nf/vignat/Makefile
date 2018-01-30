# allow the use of extglob in paths
SHELL=/bin/bash -O extglob -c

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
CFLAGS += -O3
#CFLAGS += -O0 -g -rdynamic -DENABLE_LOG -Wfatal-errors
CFLAGS += -I../..
CFLAGS += -std=gnu99

# disable warnings triggered by DPDK
CFLAGS += -Wno-implicit-function-declaration
CFLAGS += -Wno-nested-externs

include $(RTE_SDK)/mk/rte.extapp.mk

verify:
	rm -f *.bc # in case previous build failed after generating bc files
	clang -DKLEE_VERIFICATION \
		-D_GNU_SOURCE `# eal_thread.c requires pthread_setname_np from GNU pthread.h` \
		-DRTE_COMPILE_TIME_CPUFLAGS=424242 `# sentinel value; cpuflags uses it, usually passed from the dpdk build system` \
		-I . -I .. -I ../lib/stubs \
		-I $(KLEE_INCLUDE) \
		-I $(RTE_SDK)/$(RTE_TARGET)/include \
		-I $(RTE_SDK)/drivers/bus/vdev `# for stub driver` \
		--include=sse_stubs.h --include=builtin_stubs.h \
		--include=rte_config.h `# required by many DPDK files` \
		../lib/stubs/external_stub.c \
		../lib/stubs/hardware_stub.c \
		../lib/stubs/rte_stub.c \
		../nf_main.c \
		../lib/nf_util.c ../lib/nat_config.c \
		../lib/stubs/my-time-stub.c \
		flowtable.c flowmanager.c ../lib/flow.c ../lib/flow-log.c \
		loop-stub.c ../lib/stubs/containers/double-chain-stub.c \
		../lib/stubs/expirator-stub.c ../lib/stubs/containers/double-map-stub.c \
		`# Platform-independent EAL. cpuflags uses CPU intrinsics` \
		$(RTE_SDK)/lib/librte_eal/common/*.c \
		-I $(RTE_SDK)/lib/librte_eal/common `# eal_thread.c requires eal_private.h in there` \
		`# Linux-specific EAL` \
		$(RTE_SDK)/lib/librte_eal/linuxapp/eal/*.c \
		`# Other libs. acl and distributor uses CPU intrinsics (there is a generic version of distributor, but we don't need it)` \
		`#             power has been broken for a while: http://dpdk.org/ml/archives/dev/2016-February/033152.html` \
		$(RTE_SDK)/lib/!(librte_acl|librte_distributor|librte_power)/*.c \
		`# Stacks for mempool` \
		$(RTE_SDK)/drivers/mempool/stack/*.c \
		`# PCI driver support` \
		$(RTE_SDK)/drivers/bus/pci/*.c \
		$(RTE_SDK)/drivers/bus/pci/linux/*.c \
		-I $(RTE_SDK)/drivers/bus/pci `# linux pci requires private.h in there` \
		`# ixgbe driver (except bypass, SSE and ARM NEON stuff)` \
		$(RTE_SDK)/drivers/net/ixgbe/!(ixgbe_bypass|ixgbe_82599_bypass|ixgbe_rxtx_vec_sse|ixgbe_rxtx_vec_neon).c \
		$(RTE_SDK)/drivers/net/ixgbe/base/*.c \
		`# VigNAT` \
		nat_forward_vignat.c \
		-c -g -emit-llvm -fsanitize=signed-integer-overflow
	llvm-link -o veri.bc *.bc
	# if something takes longer than expected, try --max-solver-time=3 --debug-report-symbdex
        # can't use -optimize because does inlining and removes functions that we need to trace or use for aliases
	klee -libc=uclibc -no-externals -dump-call-traces -max-memory=20000 -dump-call-trace-prefixes -solver-backend=z3 -exit-on-error \
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
