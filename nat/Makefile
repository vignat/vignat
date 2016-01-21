#   BSD LICENSE
#
#   Copyright(c) 2010-2014 Intel Corporation. All rights reserved.
#   All rights reserved.
#
#   Redistribution and use in source and binary forms, with or without
#   modification, are permitted provided that the following conditions
#   are met:
#
#     * Redistributions of source code must retain the above copyright
#       notice, this list of conditions and the following disclaimer.
#     * Redistributions in binary form must reproduce the above copyright
#       notice, this list of conditions and the following disclaimer in
#       the documentation and/or other materials provided with the
#       distribution.
#     * Neither the name of Intel Corporation nor the names of its
#       contributors may be used to endorse or promote products derived
#       from this software without specific prior written permission.
#
#   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
#   "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
#   LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
#   A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
#   OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
#   SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
#   LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
#   DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
#   THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
#   (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
#   OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

ifeq ($(RTE_SDK),)
$(error "Please define RTE_SDK environment variable")
endif

# Default target, can be overriden by command line or environment
RTE_TARGET ?= x86_64-native-linuxapp-gcc

include $(RTE_SDK)/mk/rte.vars.mk

# binary name
APP = nat

# all source are stored in SRCS-y
SRCS-y := main.c lib/flowtable.c lib/flowmanager.c lib/flow.c lib/containers/map.c lib/containers/double-chain.c lib/containers/double-chain-imp.c lib/containers/double-map.c lib/containers/double-map-impl.c lib/expirator.c lib/my-time.c

CFLAGS += $(USER_FLAGS)
CFLAGS += $(WERROR_FLAGS)
LDFLAGS += 

# workaround for a gcc bug with noreturn attribute
# http://gcc.gnu.org/bugzilla/show_bug.cgi?id=12603
ifeq ($(CONFIG_RTE_TOOLCHAIN_GCC),y)
CFLAGS_main.o += -Wno-return-type
endif

include $(RTE_SDK)/mk/rte.extapp.mk

verify:
	clang-3.4 -DKLEE_VERIFICATION main.c lib/stubs/rte_stubs.c lib/stubs/flowtable-stub.c lib/flowmanager.c lib/flow.c lib/stubs/containers/double-chain-stub.c lib/stubs/expirator-stub.c lib/stubs/my-time-stub.c $(RTE_SDK)/lib/librte_cmdline/cmdline_parse*addr.c -I . -I $(KLEE_INCLUDE) -I $(RTE_SDK)/$(RTE_TARGET)/include -c -g -emit-llvm
	llvm-link-3.4 rte_stubs.bc main.bc flowtable-stub.bc flowmanager.bc flow.bc double-chain-stub.bc expirator-stub.bc my-time-stub.bc cmdline_parse*addr.bc -o veri.bc
	klee --libc=uclibc --posix-runtime veri.bc -p 0x3 --wan 1
