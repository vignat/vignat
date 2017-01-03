#!/bin/bash
. ~/scripts/config.sh

echo "[init] Initializing DPDK on tester..."
. ~/scripts/util/dpdk-functions.sh
set_numa_pages
load_igb_uio_module

echo "[init] Binding tester interfaces to DPDK..."
bind_nics_to_igb_uio $TESTER_PCI_INTERNAL
bind_nics_to_igb_uio $TESTER_PCI_EXTERNAL
