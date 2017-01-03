#!/bin/bash

echo "[clean] Unbinding middlebox interfaces from Linux..."
sudo ifconfig $MB_DEVICE_INTERNAL down
sudo ifconfig $MB_DEVICE_EXTERNAL down
sudo ifconfig $MB_DEVICE_TO_SRV down

echo "[clean] Unbinding middlebox interfaces from DPDK..."
$RTE_SDK/tools/dpdk-devbind.py -u $MB_PCI_INTERNAL
$RTE_SDK/tools/dpdk-devbind.py -u $MB_PCI_EXTERNAL
$RTE_SDK/tools/dpdk-devbind.py -u $MB_PCI_TO_SRV

echo "[clean] Killing the NAT on middlebox..."
sudo pkill -9 nat
