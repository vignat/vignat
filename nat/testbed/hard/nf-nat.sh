pkill -9 nat
sudo ~/dpdk/tools/dpdk_nic_bind.py -u 0000:02:00.1
sudo ~/dpdk/tools/dpdk_nic_bind.py -u 0000:02:00.2

ifconfig em2 up
ip addr add 192.168.2.2/24 dev em2
ifconfig em3 up
ip addr add 192.168.3.2/24 dev em3

sysctl -w net.ipv4.ip_forward=1
echo "net.ipv4.ip_forward=1" >> /etc/sysctl.conf

iptables -t nat -A POSTROUTING -o em2 -j MASQUERADE
iptables -A FORWARD -i em3 -o em2 -m state --state RELATED,ESTABLISHED -j ACCEPT
iptables -A FORWARD -i em3 -o em2 -j ACCEPT
