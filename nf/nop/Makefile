include $(RTE_SDK)/mk/rte.vars.mk

# binary name
APP = nat

# sources
SRCS-y := nat_forward_nop.c ../nf_main.c ../lib/nat_config.c ../lib/nf_time.c ../lib/nf_util.c

# gcc flags
CFLAGS += -O3
CFLAGS += -I.. -I../..
CFLAGS += -std=gnu99

# disable warnings triggered by DPDK
CFLAGS += -Wno-implicit-function-declaration
CFLAGS += -Wno-nested-externs

include $(RTE_SDK)/mk/rte.extapp.mk
