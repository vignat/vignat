include $(RTE_SDK)/mk/rte.vars.mk

# binary name
APP = bridge

# sources
SRCS-y := bridge_forward.c ../nf_main.c bridge_config.c bridge_data.c \
          ../lib/containers/map.c ../lib/containers/vector.c \
          ../lib/nf_time.c \
          ../lib/nf_util.c ../lib/containers/map-impl.c \
          ../lib/containers/double-chain.c \
          ../lib/containers/double-chain-impl.c \
          ../lib/expirator.c \
          ../lib/containers/double-map.c
# FIXME: ^^ double-map.c is unnecessary, but expirator.c virtually depends on it


# gcc flags
CFLAGS += -O3
CFLAGS += -I../..
CFLAGS += -std=gnu99

# disable warnings triggered by DPDK
CFLAGS += -Wno-implicit-function-declaration
CFLAGS += -Wno-nested-externs

include $(RTE_SDK)/mk/rte.extapp.mk


verify:
	clang -DKLEE_VERIFICATION \
		-I . -I .. -I $(KLEE_INCLUDE) -I $(RTE_SDK)/$(RTE_TARGET)/include \
		../lib/stubs/rte_stubs.c bridge_config.c ../lib/nf_util.c \
		../lib/stubs/my-time-stub.c \
		../lib/stubs/containers/map-stub.c \
		../lib/stubs/containers/vector-stub.c \
		../lib/stubs/containers/double-chain-stub.c \
		../lib/stubs/expirator-stub.c \
		$(RTE_SDK)/lib/librte_cmdline/cmdline_parse*addr.c \
    bridge_forward.c bridge_config.c bridge_data.c \
		../nf_main.c \
		-c -g -emit-llvm -fsanitize=unsigned-integer-overflow \
		-fsanitize=signed-integer-overflow
	llvm-link -o veri.bc \
		rte_stubs.bc bridge_forward.bc bridge_data.bc \
		nf_main.bc nf_util.bc bridge_config.bc \
		my-time-stub.bc expirator-stub.bc \
		map-stub.bc double-chain-stub.bc vector-stub.bc \
		cmdline_parse*addr.bc
	klee --libc=uclibc --posix-runtime --dump-call-traces --max-memory=12000 --dump-call-trace-prefixes \
		veri.bc --expire 10 --capacity 100 --config no-file.cfg
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
		../lib/containers/vector.c \
		../lib/containers/map.c \
		bridge_data.c
