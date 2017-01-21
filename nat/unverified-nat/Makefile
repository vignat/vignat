include $(RTE_SDK)/mk/rte.vars.mk

# binary name
APP = nat

# C++ compiler
CC = g++

# sources
SRCS-y := nat_forward_nat.c nat_map_dpdk.c ../nat_main.c ../nat_config.c ../nat_time.c ../nat_util.c

# g++ flags
CFLAGS += -O0 -g -rdynamic -DENABLE_LOG
#CFLAGS += -O3
CFLAGS += -I..
CFLAGS += -std=gnu++11

LDFLAGS += -lstdc++

include $(RTE_SDK)/mk/rte.extapp.mk
