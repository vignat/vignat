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
		-I . -I .. -I ../lib/stubs -I $(KLEE_INCLUDE) -I $(RTE_SDK)/$(RTE_TARGET)/include \
		--include=sse_stubs.h --include=builtin_stubs.h \
		--include=rte_config.h `# required by many DPDK files` \
		-I $(RTE_SDK)/lib/librte_eal/common `# eal_thread.c requires eal_private.h in there` \
		../lib/stubs/device_stub.c \
		../nf_main.c \
		../lib/nf_util.c ../lib/nat_config.c \
		../lib/stubs/my-time-stub.c \
		flowtable.c flowmanager.c ../lib/flow.c ../lib/flow-log.c \
		loop-stub.c ../lib/stubs/containers/double-chain-stub.c \
		../lib/stubs/expirator-stub.c ../lib/stubs/containers/double-map-stub.c \
		`# Platform-independent EAL. cpuflags uses CPU intrinsics, xen_memory is only for Xen` \
		$(RTE_SDK)/lib/librte_eal/common/!(eal_common_cpuflags|eal_xen_memory).c \
		`# Linux-specific EAL. xen_memory is only for Xen` \
		$(RTE_SDK)/lib/librte_eal/linuxapp/eal/!(eal_xen_memory).c \
		`# Other libs. acl and hash use CPU intrinsics, power and ivshmem are broken as of DPDK 16.07` \
		$(RTE_SDK)/lib/!(librte_acl|librte_hash|librte_power|librte_ivshmem)/*.c \
		nat_forward_vignat.c  \
		-c -g -emit-llvm -fsanitize=signed-integer-overflow
	llvm-link -o veri.bc *.bc
	# if something takes longer than expected, try --max-solver-time=3 --debug-report-symbdex
        # note: as of 2018-01-10, can't use --optimize because it creates a ShuffleVector instr in KLEE's own memmove, which KLEE doesn't support...
	klee -libc=uclibc -posix-runtime -all-external-warnings -dump-call-traces -max-memory=12000 -dump-call-trace-prefixes -solver-backend=z3 -exit-on-error \
		veri.bc \
		--no-pci `# disable PCI enumeration since PCI is not available, we don't it use anyway` \
		--no-huge -m 1 `# use 1 MB of malloc'ed memory instead of hugepages` \
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
