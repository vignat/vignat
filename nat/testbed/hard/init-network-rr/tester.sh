#!/bin/bash
. ~/scripts/config.sh

echo "[init] Initializing DPDK on tester..."
. ~/scripts/util/dpdk-functions.sh
set_numa_pages
load_igb_uio_module

echo "[init] Binding TESTER_DEVICE_EXTERNAL to DPDK..."
bind_nics_to_igb_uio $TESTER_PCI_EXTERNAL

echo "[init] Configuring tester IP..."
sudo ifconfig $TESTER_DEVICE_INTERNAL up
sudo ip addr flush dev $TESTER_DEVICE_INTERNAL
sudo ip addr add $TESTER_IP_INTERNAL/24 dev $TESTER_DEVICE_INTERNAL

echo "[init] Configuring tester route..."
sudo ip route flush $SERVER_SUBNET
sudo ip route add $SERVER_SUBNET/24 via $MB_IP_INTERNAL dev $TESTER_DEVICE_INTERNAL
sudo ip route flush cache
sudo arp -s $MB_IP_INTERNAL $MB_MAC_INTERNAL

echo "[init] Configuring tester connection reuse speed..."
. ~/scripts/util/relieve-connection-reuse.sh
