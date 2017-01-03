#!/bin/bash
. ~/scripts/config.sh

echo "[init] Configuring server IP..."
ifconfig $SERVER_DEVICE up
ip addr flush dev $SERVER_DEVICE
ip addr add $SERVER_IP/24 dev $SERVER_DEVICE
arp -s $MB_IP_TO_SRV $MB_MAC_TO_SRV

echo "[init] Configuring server connection reuse speed..."
. ~/scripts/util/relieve-connection-reuse.sh
