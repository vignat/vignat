#!/bin/bash
. ./config.sh

echo "[init] Unbinding middlebox interfaces from DPDK..."
sudo ~/dpdk/tools/dpdk-devbind.py -b igb $MB_PCI_INTERNAL $MB_PCI_EXTERNAL $MB_PCI_TO_SRV
sleep 8

echo "[init] Configuring middlebox IPs..."
ifconfig $MB_DEVICE_TO_SRV up
ip addr flush dev $MB_DEVICE_TO_SRV
ip addr add $MB_IP_TO_SRV/24 dev $MB_DEVICE_TO_SRV
ifconfig $MB_DEVICE_INTERNAL up
ip addr flush dev $MB_DEVICE_INTERNAL
ip addr add $MB_IP_INTERNAL/24 dev $MB_DEVICE_INTERNAL
ifconfig $MB_DEVICE_EXTERNAL up
ip addr flush dev $MB_DEVICE_EXTERNAL
ip addr add $MB_IP_EXTERNAL/24 dev $MB_DEVICE_EXTERNAL

echo "[init] Configuring middlebox forwarding rules..."
sysctl -w net.ipv4.ip_forward=1
echo "net.ipv4.ip_forward=1" >> /etc/sysctl.conf

iptables -F FORWARD
iptables -t nat -F POSTROUTING
iptables -t nat -A POSTROUTING -o $MB_DEVICE_TO_SRV -j MASQUERADE
iptables -A FORWARD -i $MB_DEVICE_INTERNAL -o $MB_DEVICE_TO_SRV -m state --state NEW,RELATED,ESTABLISHED -j ACCEPT
iptables -A FORWARD -i $MB_DEVICE_INTERNAL -o $MB_DEVICE_TO_SRV -j ACCEPT
iptables -A FORWARD -i $MB_DEVICE_EXTERNAL -o $MB_DEVICE_TO_SRV -m state --state NEW,RELATED,ESTABLISHED -j ACCEPT
iptables -A FORWARD -i $MB_DEVICE_EXTERNAL -o $MB_DEVICE_TO_SRV -j ACCEPT

arp -s $SERVER_IP $SERVER_MAC
arp -s $TESTER_IP_INTERNAL $TESTER_MAC_INTERNAL
arp -s $TESTER_IP_EXTERNAL $TESTER_MAC_EXTERNAL

echo "[init] Unlocking software restrictions on middlebox NetFilter..."
. ./util/netfilter-unlock.sh $MB_DEVICE_TO_SRV
