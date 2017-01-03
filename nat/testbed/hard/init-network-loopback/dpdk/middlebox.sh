#!/bin/bash
. ./config.sh

echo "[init] Initializing DPDK on middlebox..."
. ./util/dpdk-setup-functions.sh
set_numa_pages
load_igb_uio_module

echo "[init] Unbinding unused middlebox interface from DPDK..."
$RTE_SDK/tools/dpdk-devbind.py -u $MB_PCI_TO_SRV

echo "[init] Binding middlebox interfaces to DPDK..."
sudo ifconfig $MB_DEVICE_INTERNAL down
sudo ifconfig $MB_DEVICE_EXTERNAL down

bind_nics_to_igb_uio $MB_PCI_INTERNAL
bind_nics_to_igb_uio $MB_PCI_EXTERNAL
