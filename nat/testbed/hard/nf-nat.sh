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
iptables -A FORWARD -i $NAT_DEVICE_INTERNAL -o $NAT_DEVICE_EXTERNAL -m state --state RELATED,ESTABLISHED -j ACCEPT
iptables -A FORWARD -i $NAT_DEVICE_INTERNAL -o $NAT_DEVICE_EXTERNAL -j ACCEPT
