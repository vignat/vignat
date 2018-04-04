#!/bin/bash

export DPDK_NIC_DRIVER=igb_uio
export RTE_SDK=$HOME/dpdk
export RTE_TARGET=x86_64-native-linuxapp-gcc

echo "[clean] Unbinding interfaces from Linux..."
sudo ifconfig em2 down
sudo ifconfig em3 down
sudo ifconfig em4 down

echo "[init] Initializing DPDK..."
. ./dpdk-functions.sh
set_numa_pages
load_igb_uio_module

echo "[init] Binding interfaces to DPDK..."
bind_nics_to_igb_uio "0000:02:00.1"
bind_nics_to_igb_uio "0000:02:00.2"
bind_nics_to_igb_uio "0000:02:00.3"
