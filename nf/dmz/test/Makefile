include $(RTE_SDK)/mk/rte.vars.mk

# binary name
APP = dmz-test

# sources
SRCS-y := dmz_test.c ../dmz_main.c ../dmz_config.c ../../lib/nf_time.c ../../lib/nf_util.c \
          ../../lib/flow.c ../../lib/flow-log.c ../../lib/flowmanager.c ../../lib/flowtable.c \
          ../../lib/expirator.c \
          ../../lib/containers/double-chain.c ../../lib/containers/double-chain-impl.c \
          ../../lib/containers/map-impl.c ../../lib/containers/double-map.c \
          ../../lib/containers/vector.c ../../lib/containers/map.c
# gcc flags
CFLAGS += -O3
CFLAGS += -I..
CFLAGS += -I../..
CFLAGS += -I../../..
CFLAGS += -std=gnu99

#CFLAGS += -DENABLE_LOG

# disable warnings triggered by DPDK
CFLAGS += -Wno-implicit-function-declaration
CFLAGS += -Wno-nested-externs

include $(RTE_SDK)/mk/rte.extapp.mk
