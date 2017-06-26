include $(RTE_SDK)/mk/rte.vars.mk

# binary name
APP = nat

# C++ compiler
CC = g++

# sources
SRCS-y := nat_forward_nat.c nat_map_dpdk.c ../nf_main.c ../lib/nat_config.c ../lib/nf_time.c ../lib/nf_util.c

# g++ flags
CFLAGS += -O3
CFLAGS += -I..
CFLAGS += -std=gnu++11

LDFLAGS += -lstdc++

include $(RTE_SDK)/mk/rte.extapp.mk
