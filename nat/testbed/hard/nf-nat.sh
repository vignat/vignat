pkill -9 nat
echo "unbinding em2, em3"
sudo ~/dpdk/tools/dpdk_nic_bind.py -b igb 0000:02:00.1 0000:02:00.2

sleep 8
echo "configuring ip addresses"
ifconfig em2 up
ip addr add 192.168.2.2/24 dev em2
ifconfig em3 up
ip addr add 192.168.3.2/24 dev em3

sysctl -w net.ipv4.ip_forward=1
echo "net.ipv4.ip_forward=1" >> /etc/sysctl.conf

echo "wiping old iptables rules"
iptables -F FORWARD
iptables -t nat -F POSTROUTING

echo "installing forwarding rules"
iptables -t nat -A POSTROUTING -o em2 -j MASQUERADE
iptables -A FORWARD -i em3 -o em2 -m state --state RELATED,ESTABLISHED -j ACCEPT
iptables -A FORWARD -i em3 -o em2 -j ACCEPT
