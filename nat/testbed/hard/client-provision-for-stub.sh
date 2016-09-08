. ./config.sh

ifconfig $CLIENT_DEVICE_DIRECT up
ip addr flush dev $CLIENT_DEVICE_DIRECT
ip addr add $CLIENT_IP_DIRECT/24 dev $CLIENT_DEVICE_DIRECT
ifconfig $CLIENT_DEVICE_INDIRECT up
ip addr flush dev $CLIENT_DEVICE_INDIRECT
ip addr add $CLIENT_IP_FOR_STUB/24 dev $CLIENT_DEVICE_INDIRECT
ip route flush $EXTERNAL_SUBNET
ip route flush cache
arp -s $SERVER_IP_INDIRECT $NAT_INTERNAL_MAC
#hping3 192.168.33.10 -k -p 47882 -s 0
