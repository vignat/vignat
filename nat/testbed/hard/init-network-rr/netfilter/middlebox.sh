#!/bin/bash
. ./config.sh
. ./util/functions.sh

echo "[init] Configuring middlebox IPs..."
sudo ifconfig $MB_DEVICE_TO_SRV up
sudo ip addr flush dev $MB_DEVICE_TO_SRV
sudo ip addr add $MB_IP_TO_SRV/24 dev $MB_DEVICE_TO_SRV
sudo ifconfig $MB_DEVICE_INTERNAL up
sudo ip addr flush dev $MB_DEVICE_INTERNAL
sudo ip addr add $MB_IP_INTERNAL/24 dev $MB_DEVICE_INTERNAL
sudo ifconfig $MB_DEVICE_EXTERNAL up
sudo ip addr flush dev $MB_DEVICE_EXTERNAL
sudo ip addr add $MB_IP_EXTERNAL/24 dev $MB_DEVICE_EXTERNAL

echo "[init] Configuring middlebox forwarding rules..."
sudo sysctl -w net.ipv4.ip_forward=1
sudo_append /etc/sysctl.conf "net.ipv4.ip_forward=1"

sudo iptables -F FORWARD
sudo iptables -t nat -F POSTROUTING
sudo iptables -t nat -A POSTROUTING -o $MB_DEVICE_TO_SRV -j MASQUERADE
sudo iptables -A FORWARD -i $MB_DEVICE_INTERNAL -o $MB_DEVICE_TO_SRV -m state --state NEW,RELATED,ESTABLISHED -j ACCEPT
sudo iptables -A FORWARD -i $MB_DEVICE_INTERNAL -o $MB_DEVICE_TO_SRV -j ACCEPT
sudo iptables -A FORWARD -i $MB_DEVICE_EXTERNAL -o $MB_DEVICE_TO_SRV -m state --state NEW,RELATED,ESTABLISHED -j ACCEPT
sudo iptables -A FORWARD -i $MB_DEVICE_EXTERNAL -o $MB_DEVICE_TO_SRV -j ACCEPT

sudo arp -s $SERVER_IP $SERVER_MAC
sudo arp -s $TESTER_IP_INTERNAL $TESTER_MAC_INTERNAL
sudo arp -s $TESTER_IP_EXTERNAL $TESTER_MAC_EXTERNAL

echo "[init] Unlocking software restrictions on middlebox NetFilter..."
. ./util/netfilter-unlock.sh $MB_DEVICE_TO_SRV
