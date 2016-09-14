. ./config.sh

pkill -9 nat
echo "unbinding $NAT_PCI_INTERNAL, $NAT_PCI_EXTERNAL"
sudo ~/dpdk/tools/dpdk-devbind.py -b igb $NAT_PCI_INTERNAL $NAT_PCI_EXTERNAL

sleep 8
echo "configuring ip addresses"
ifconfig $NAT_DEVICE_EXTERNAL up
ip addr flush dev $NAT_DEVICE_EXTERNAL
ip addr add $NAT_IP_EXTERNAL/24 dev $NAT_DEVICE_EXTERNAL
ifconfig $NAT_DEVICE_INTERNAL up
ip addr flush dev $NAT_DEVICE_INTERNAL
ip addr add $NAT_IP_INTERNAL/24 dev $NAT_DEVICE_INTERNAL

sysctl -w net.ipv4.ip_forward=1
echo "net.ipv4.ip_forward=1" >> /etc/sysctl.conf

echo "wiping old iptables rules"
iptables -F FORWARD
iptables -t nat -F POSTROUTING

echo "installing forwarding rules"
iptables -t nat -A POSTROUTING -o $NAT_DEVICE_EXTERNAL -j MASQUERADE
iptables -A FORWARD -i $NAT_DEVICE_INTERNAL -o $NAT_DEVICE_EXTERNAL -m state --state NEW,RELATED,ESTABLISHED -j ACCEPT
iptables -A FORWARD -i $NAT_DEVICE_INTERNAL -o $NAT_DEVICE_EXTERNAL -j ACCEPT

arp -s 192.168.2.10 00:1e:67:92:2a:bc
arp -s 192.168.3.5 00:1e:67:92:2a:bd

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
ifconfig em2 txqueuelen 10000
