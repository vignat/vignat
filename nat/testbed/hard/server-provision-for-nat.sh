. config.sh

ifconfig $DEVICE_INDIRECT up
ip addr flush dev $DEVICE_INDIRECT
ip addr add $SERVER_IP_INDIRECT/24 dev $DEVICE_INDIRECT
ifconfig $DEVICE_DIRECT up
ip addr flush dev $DEVICE_DIRECT
ip addr add $SERVER_IP_DIRECT/24 dev $DEVICE_DIRECT
arp -s NAT_IP_EXTERNAL $NAT_EXTERNAL_MAC
#hping3 192.168.33.10 -k -p 47882 -s 0
