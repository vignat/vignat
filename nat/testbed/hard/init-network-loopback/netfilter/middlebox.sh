#!/bin/bash
. ./config.sh

echo "[init] Configuring middlebox IPs..."
ifconfig $MB_DEVICE_EXTERNAL up
ip addr flush dev $MB_DEVICE_EXTERNAL
ip addr add $MB_IP_EXTERNAL/24 dev $MB_DEVICE_EXTERNAL
ifconfig $MB_DEVICE_INTERNAL up
ip addr flush dev $MB_DEVICE_INTERNAL
ip addr add $MB_IP_INTERNAL/24 dev $MB_DEVICE_INTERNAL
ifconfig $MB_DEVICE_TO_SRV down

echo "[init] Configuring middlebox forwarding rules..."
sysctl -w net.ipv4.ip_forward=1
echo "net.ipv4.ip_forward=1" >> /etc/sysctl.conf

iptables -F FORWARD
iptables -t nat -F POSTROUTING
iptables -t nat -A POSTROUTING -o $MB_DEVICE_EXTERNAL -j MASQUERADE
iptables -A FORWARD -i $MB_DEVICE_INTERNAL -o $MB_DEVICE_EXTERNAL -m state --state NEW,RELATED,ESTABLISHED -j ACCEPT
iptables -A FORWARD -i $MB_DEVICE_INTERNAL -o $MB_DEVICE_EXTERNAL -j ACCEPT

arp -s $TESTER_IP_EXTERNAL $TESTER_MAC_EXTERNAL
arp -s $TESTER_IP_INTERNAL $TESTER_MAC_INTERNAL

echo "[init] Unlocking software restrictions on middlebox NetFilter..."
. ./util/netfilter-unlock.sh $MB_DEVICE_EXTERNAL
