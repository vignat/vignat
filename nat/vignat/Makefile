include $(RTE_SDK)/mk/rte.vars.mk

# binary name
APP = nat

# sources
SRCS-y := nat_forward_vignat.c ../nat_main.c ../nat_config.c ../nat_time.c ../nat_util.c \
          lib/flow.c lib/flow-log.c lib/flowmanager.c lib/flowtable.c \
          lib/expirator.c \
          lib/containers/double-chain.c lib/containers/double-chain-impl.c \
          lib/containers/map.c lib/containers/double-map.c

# gcc flags
CFLAGS += -O3
#CFLAGS += -O0 -g -rdynamic -DENABLE_LOG -Wfatal-errors
CFLAGS += -I..
CFLAGS += -std=gnu99

# disable warnings triggered by DPDK
CFLAGS += -Wno-implicit-function-declaration
CFLAGS += -Wno-nested-externs

include $(RTE_SDK)/mk/rte.extapp.mk

verify:
	clang -DKLEE_VERIFICATION \
		-I . -I $(KLEE_INCLUDE) -I $(RTE_SDK)/$(RTE_TARGET)/include \
		nat_forward_vignat.c nat_main_stub.c ../nat_config.c nat_util_stub.c \
		lib/stubs/my-time-stub.c \
		lib/stubs/rte_stubs.c \
		lib/flowtable.c lib/flowmanager.c lib/flow.c lib/flow-log.c \
		lib/stubs/loop-stub.c lib/stubs/containers/double-chain-stub.c lib/stubs/expirator-stub.c lib/stubs/containers/double-map-stub.c \
		$(RTE_SDK)/lib/librte_cmdline/cmdline_parse*addr.c \
		-c -g -emit-llvm -fsanitize=unsigned-integer-overflow -fsanitize=signed-integer-overflow
	llvm-link -o veri.bc \
		nat_forward_vignat.bc nat_main_stub.bc nat_config.bc nat_util_stub.bc \
		my-time-stub.bc \
		rte_stubs.bc \
		flowtable.bc flowmanager.bc flow.bc flow-log.bc \
		loop-stub.bc double-chain-stub.bc expirator-stub.bc double-map-stub.bc \
		cmdline_parse*addr.bc
	klee --libc=uclibc --posix-runtime --dump-call-traces --max-memory=12000 --dump-call-trace-prefixes \
		veri.bc --devs-mask 0x3 --wan 1 --lan-dev 0 --expire 10 --starting-port 0 --max-flows 65536
	rm *.bc

verifast:
	verifast -I . -allow_assume -shared \
		lib/assumptions_stubs.c \
		lib/containers/double-chain-impl.c lib/containers/double-chain.c lib/containers/map.c lib/containers/double-map.c \
 		lib/containers/batcher.c lib/coherence.c lib/expirator.c \
		lib/containers/array-bat-verifast.c lib/containers/array-rq-verifast.c lib/containers/array-u16-verifast.c lib/containers/array-lcc-verifast.c \
		abstract-state-verify-lemmas.c
