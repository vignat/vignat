. config.sh

ifconfig $DEVICE_DIRECT up
ip addr flush dev $DEVICE_DIRECT
ip addr add $CLIENT_IP_DIRECT/24 dev $DEVICE_DIRECT
ifconfig $DEVICE_INDIRECT up
ip addr flush dev $DEVICE_INDIRECT
ip addr add $CLIENT_IP_INDIRECT/24 dev $DEVICE_INDIRECT
ip route add $INTERNAL_SUBNET/24 via $NAT_IP_INTERNAL dev $DEVICE_INDIRECT
arp -s $NAT_IP_INTERNAL $NAT_INTERNAL_MAC
#hping3 192.168.33.10 -k -p 47882 -s 0
