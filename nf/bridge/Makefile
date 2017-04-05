include $(RTE_SDK)/mk/rte.vars.mk

# binary name
APP = bridge

# sources
SRCS-y := bridge_forward.c ../nf_main.c bridge_config.c ../lib/nf_time.c ../lib/nf_util.c ../lib/containers/map.c ../lib/containers/double-chain.c ../lib/containers/double-chain-impl.c

# gcc flags
CFLAGS += -O3
CFLAGS += -I../..
CFLAGS += -std=gnu99

# disable warnings triggered by DPDK
CFLAGS += -Wno-implicit-function-declaration
CFLAGS += -Wno-nested-externs

include $(RTE_SDK)/mk/rte.extapp.mk
