#!/bin/bash
# Set up NetFilter NAT (i.e. iptables MASQUERADE) for the loopback scenario.
# The second part of the script tries to remove the artificially
# software limits, to unleash the real power of NetFilter.

. ./config.sh

pkill -9 nat
echo "unbinding $MB_PCI_INTERNAL, $MB_PCI_EXTERNAL, $MB_PCI_TO_SRV"
sudo ~/dpdk/tools/dpdk-devbind.py -b igb $MB_PCI_INTERNAL $MB_PCI_EXTERNAL $MB_PCI_TO_SRV

sleep 8
echo "configuring ip addresses"
ifconfig $MB_DEVICE_EXTERNAL up
ip addr flush dev $MB_DEVICE_EXTERNAL
ip addr add $MB_IP_EXTERNAL/24 dev $MB_DEVICE_EXTERNAL
ifconfig $MB_DEVICE_INTERNAL up
ip addr flush dev $MB_DEVICE_INTERNAL
ip addr add $MB_IP_INTERNAL/24 dev $MB_DEVICE_INTERNAL
ifconfig $MB_DEVICE_TO_SRV down

sysctl -w net.ipv4.ip_forward=1
echo "net.ipv4.ip_forward=1" >> /etc/sysctl.conf

echo "wiping old iptables rules"
iptables -F FORWARD
iptables -t nat -F POSTROUTING

echo "installing forwarding rules"
iptables -t nat -A POSTROUTING -o $MB_DEVICE_EXTERNAL -j MASQUERADE
iptables -A FORWARD -i $MB_DEVICE_INTERNAL -o $MB_DEVICE_EXTERNAL -m state --state NEW,RELATED,ESTABLISHED -j ACCEPT
iptables -A FORWARD -i $MB_DEVICE_INTERNAL -o $MB_DEVICE_EXTERNAL -j ACCEPT

arp -s $TESTER_IP_EXTERNAL $TESTER_MAC_EXTERNAL
arp -s $TESTER_IP_INTERNAL $TESTER_MAC_INTERNAL

# 4KB send buffer, 20,480 connections max at worst case
echo 83886080  > /proc/sys/net/core/wmem_max
echo 83886080  > /proc/sys/net/core/wmem_default
# 16KB receive buffer, 20,480 connections max at worst case
echo 335544320 > /proc/sys/net/core/rmem_max
echo 335544320 > /proc/sys/net/core/rmem_default
# Max open files
# already bigger: echo 65536 > /proc/sys/fs/file­max
# Fast port recycling (TIME_WAIT)
echo 1 >/proc/sys/net/ipv4/tcp_tw_recycle
echo 1 >/proc/sys/net/ipv4/tcp_tw_reuse
# TIME_WAIT buckets increased
# already bigger: echo 65536 > /proc/sys/net/ipv4/tcp_max_tw_buckets
# FIN timeout decreased
echo 15 > /proc/sys/net/ipv4/tcp_fin_timeout
# SYN backlog increased
echo 65536 > /proc/sys/net/ipv4/tcp_max_syn_backlog
# SYN cookies enabled
echo 1 > /proc/sys/net/ipv4/tcp_syncookies
# Local port range maximized
echo "1024 65535" > /proc/sys/net/ipv4/ip_local_port_range
# Netdev backlog increased
echo 100000 > /proc/sys/net/core/netdev_max_backlog
# Interface transmit queuelen increased
ifconfig $MB_DEVICE_EXTERNAL txqueuelen 10000
