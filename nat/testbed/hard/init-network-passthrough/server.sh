#!/bin/bash
. ~/scripts/config.sh

echo "[init] Configuring server IP..."
sudo ifconfig $SERVER_DEVICE up
sudo ip addr flush dev $SERVER_DEVICE
sudo ip addr add $SERVER_IP/24 dev $SERVER_DEVICE
sudo arp -s $TESTER_IP_FOR_STUB $MB_MAC_TO_SRV

echo "[init] Configuring server connection reuse speed..."
. ~/scripts/util/relieve-connection-reuse.sh
