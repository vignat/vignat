include $(RTE_SDK)/mk/rte.vars.mk

# binary name
APP = nat

# sources
SRCS-y := nat_forward_nop.c ../nat_main.c ../nat_config.c ../nat_time.c ../nat_util.c

# gcc flags
CFLAGS += -O3
CFLAGS += -I..
CFLAGS += -std=gnu99

# batch size, if available
ifdef NAT_BATCH_SIZE
CFLAGS += -DBATCH_SIZE=$(NAT_BATCH_SIZE)
endif

# disable warnings triggered by DPDK
CFLAGS += -Wno-implicit-function-declaration
CFLAGS += -Wno-nested-externs

include $(RTE_SDK)/mk/rte.extapp.mk
