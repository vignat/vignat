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
	clang -DKLEE_VERIFICATION \
		-D_GNU_SOURCE `# eal_thread.c requires pthread_setname_np from GNU pthread.h` \
		-I . -I .. -I ../lib/stubs -I $(KLEE_INCLUDE) -I $(RTE_SDK)/$(RTE_TARGET)/include \
		--include=sse_stubs.h --include=builtin_stubs.h \
		--include=klee/klee.h \
		--include=rte_config.h `# required by many DPDK files` \
		-I $(RTE_SDK)/lib/librte_eal/common `# eal_thread.c requires eal_private.h in there` \
		../lib/stubs/device_stub.c \
		../nf_main.c \
		../lib/nf_util.c ../lib/nat_config.c \
		../lib/stubs/my-time-stub.c \
		flowtable.c flowmanager.c ../lib/flow.c ../lib/flow-log.c \
		loop-stub.c ../lib/stubs/containers/double-chain-stub.c \
		../lib/stubs/expirator-stub.c ../lib/stubs/containers/double-map-stub.c \
		$(RTE_SDK)/lib/librte_eal/common/eal_common_errno.c `# for per-lcore errno` \
		$(RTE_SDK)/lib/librte_eal/common/eal_common_thread.c `# threading stuff` \
		$(RTE_SDK)/lib/librte_eal/linuxapp/eal/eal_thread.c `# linux-specific threading stuff` \
		$(RTE_SDK)/lib/librte_mempool/rte_mempool_ops.c `# for rte_mempool_ops_table` \
		$(RTE_SDK)/lib/librte_eal/linuxapp/eal/eal.c `# for lcore_config` \
		$(RTE_SDK)/lib/librte_eal/common/eal_common_lcore.c `# lcore/cpu functions` \
		$(RTE_SDK)/lib/librte_eal/linuxapp/eal/eal_lcore.c `# linux-specific lcore/cpu functions` \
		$(RTE_SDK)/lib/librte_eal/common/eal_common_log.c `# a bunch of logging functions` \
		$(RTE_SDK)/lib/librte_eal/linuxapp/eal/eal_log.c `# linux-specific logging functions` \
		$(RTE_SDK)/lib/librte_eal/common/eal_common_options.c `# configuration stuff` \
		$(RTE_SDK)/lib/librte_eal/common/eal_common_devargs.c `# args for devices` \
		$(RTE_SDK)/lib/librte_eal/linuxapp/eal/eal_hugepage_info.c `# hugepages` \
		$(RTE_SDK)/lib/librte_eal/linuxapp/eal/eal_debug.c `# rte_panic` \
		$(RTE_SDK)/lib/librte_eal/common/eal_common_string_fns.c `# string functions` \
		$(RTE_SDK)/lib/librte_eal/common/eal_common_pci.c `# PCI` \
		$(RTE_SDK)/lib/librte_eal/linuxapp/eal/eal_pci.c `# linux-specific PCI` \
		$(RTE_SDK)/lib/librte_eal/common/eal_common_memory.c `# memory` \
		$(RTE_SDK)/lib/librte_eal/linuxapp/eal/eal_memory.c `# linux-specific memory` \
		$(RTE_SDK)/lib/librte_eal/common/eal_common_memzone.c `# more memory stuff` \
		$(RTE_SDK)/lib/librte_eal/common/malloc_heap.c `# even more memory stuff` \
		$(RTE_SDK)/lib/librte_eal/common/malloc_elem.c `# even more even more memory stuff` \
		$(RTE_SDK)/lib/librte_eal/common/rte_malloc.c `# even more even more even more memory stuff` \
		$(RTE_SDK)/lib/librte_eal/common/eal_common_tailqs.c `# some kind of sys/queues wrapper for tailq` \
		$(RTE_SDK)/lib/librte_eal/linuxapp/eal/eal_alarm.c `# some kind of timer` \
		$(RTE_SDK)/lib/librte_eal/common/eal_common_timer.c `# another kind of timer` \
		$(RTE_SDK)/lib/librte_eal/linuxapp/eal/eal_timer.c `# linux-specific timer` \
		$(RTE_SDK)/lib/librte_eal/common/eal_common_dev.c `# devices` \
		$(RTE_SDK)/lib/librte_eal/linuxapp/eal/eal_interrupts.c `# interrupts` \
		`# from here on RTE_SDK stuff is required by VigNAT, above it was DPDK EAL` \
		$(RTE_SDK)/lib/librte_ether/rte_ethdev.c \
		$(RTE_SDK)/lib/librte_mbuf/rte_mbuf.c \
		$(RTE_SDK)/lib/librte_cmdline/cmdline_parse*.c \
		nat_forward_vignat.c  \
		-c -g -emit-llvm -fsanitize=signed-integer-overflow
	llvm-link -o veri.bc *.bc
	# --log-level 0 otherwise there's an error - for now, verify without logging
	klee --libc=uclibc --posix-runtime --dump-call-traces --max-memory=16000 --dump-call-trace-prefixes \
		veri.bc --log-level 0 --no-pci --no-huge --no-shconf -- \
		--lan-dev 0 --wan 1 --expire 10 --starting-port 0 --max-flows 65536 \
		--extip 10.0.0.0 --eth-dest 0,01:23:45:67:89:00 --eth-dest 1,01:23:45:67:89:01
	rm *.bc

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
