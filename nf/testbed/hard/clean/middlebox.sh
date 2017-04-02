#!/bin/bash
. ./config.sh

echo "[clean] Unbinding middlebox interfaces from Linux..."
sudo ifconfig $MB_DEVICE_INTERNAL down
sudo ifconfig $MB_DEVICE_EXTERNAL down
sudo ifconfig $MB_DEVICE_TO_SRV down

echo "[clean] Unbinding middlebox interfaces from DPDK..."
sudo $RTE_SDK/tools/dpdk-devbind.py -b $KERN_NIC_DRIVER $MB_PCI_INTERNAL $MB_PCI_EXTERNAL $MB_PCI_TO_SRV

echo "[clean] Killing the NAT on middlebox..."
sudo pkill -9 nat
