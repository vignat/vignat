#!/bin/bash

echo "[clean] Unbinding tester interfaces from Linux..."
sudo ifconfig $TESTER_DEVICE_INTERNAL down
sudo ifconfig $TESTER_DEVICE_EXTERNAL down

echo "[clean] Unbinding tester interfaces from DPDK..."
$RTE_SDK/tools/dpdk-devbind.py -u $TESTER_PCI_INTERNAL
$RTE_SDK/tools/dpdk-devbind.py -u $TESTER_PCI_EXTERNAL

echo "[clean] Killing pktgen on tester..."
sudo pkill -9 pktgen
