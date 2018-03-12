include $(RTE_SDK)/mk/rte.vars.mk

# binary name
APP = nat

# C++ compiler
CC = g++

# sources
# pick one map of: ruby, DPDK, stdlib
SRCS-y := nat_forward_nat.c ../nf_main.c ../lib/nat_config.c ../lib/nf_time.c ../lib/nf_util.c \
          ruby/st.c nat_map_ruby.c
#          nat_map_dpdk.c
#          nat_map_cppstl.c

# g++ flags
CFLAGS += -O3
CFLAGS += -I.. -I../..
CFLAGS += -std=gnu++11
# Debug only!
#CFLAGS += -DENABLE_LOG -O0 -g -rdynamic

# Ruby needs that if it's, well, not Ruby
CFLAGS += -DNOT_RUBY
# Ruby's onigmo generates a ton of these
CFLAGS += -Wno-narrowing

LDFLAGS += -lstdc++

include $(RTE_SDK)/mk/rte.extapp.mk
