#!/bin/bash
. ~/scripts/config.sh

echo "[init] Initializing DPDK on tester..."
. ~/scripts/util/dpdk-functions.sh
set_numa_pages
load_igb_uio_module

echo "[init] Binding TESTER_DEVICE_EXTERNAL to DPDK..."
sudo ifconfig $TESTER_DEVICE_EXTERNAL down
bind_nics_to_igb_uio $TESTER_PCI_EXTERNAL

echo "[init] Unbinding TESTER_PCI_INTERNAL from DPDK..."
$RTE_SDK/tools/dpdk-devbind.py -b igb $TESTER_PCI_INTERNAL
sleep 8

echo "[init] Configuring tester IP..."
ifconfig $TESTER_DEVICE_EXTERNAL down
ifconfig $TESTER_DEVICE_INTERNAL up
ip addr flush dev $TESTER_DEVICE_INTERNAL
ip addr add $TESTER_IP_FOR_STUB/24 dev $TESTER_DEVICE_INTERNAL

echo "[init] Configuring tester routes..."
ip route flush $SERVER_SUBNET
ip route flush cache
arp -s $SERVER_IP $MB_MAC_INTERNAL

echo "[init] Configuring tester connection reuse speed..."
. ~/scripts/util/relieve-connection-reuse.sh
