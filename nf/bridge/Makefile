# Binary name
APP := bridge

# Runtime and verification files
NF_FILES := bridge_forward.c bridge_config.c bridge_data.c

# Runtime files (none)
# NF_RUNTIME_FILES := ???

# Verification files
NF_VERIF_FILES := bridge_loop.c bridge_stub.c

# Verification arguments
NF_VERIF_ARGS := --expire 10 --capacity 100 --config no-file.cfg

include ../Makefile
