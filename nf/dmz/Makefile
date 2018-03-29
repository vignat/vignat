# Binary name
APP := dmz

# Runtime and verification files
NF_FILES := dmz_main.c dmz_config.c \
            ../lib/flow.c ../lib/flow-log.c \
            ../lib/flowmanager.c ../lib/flowtable.c

# Verification files
NF_VERIF_FILES := dmz_loop.c

# Verification definitions
# Need 3 devices otherwise the concept of a DMZ doesn't make sense
NF_VERIF_DEFS := -DSTUB_DEVICES_COUNT=3

# Verification arguments
NF_VERIF_ARGS := --inter-dev 0 \
                 --dmz-dev 1 \
                 --intra-dev 2 \
                 --dmz-addr 0.0.0.0 \
                 --dmz-mask 255.0.0.0 \
                 --intra-addr 1.0.0.0 \
                 --intra-mask 255.0.0.0 \
                 --expire 10 \
                 --max-flows 65536 \
                 --eth-dest 0,01:23:45:67:89:00 \
                 --eth-dest 1,01:23:45:67:89:01

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
