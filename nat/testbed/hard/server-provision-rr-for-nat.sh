# Configure the server for the request-responce (ping-pong) perf testing
# topology involving a NAT.
. ~/scripts/config.sh

ifconfig $SERVER_DEVICE up
ip addr flush dev $SERVER_DEVICE
ip addr add $SERVER_IP/24 dev $SERVER_DEVICE
arp -s $MB_IP_TO_SRV $MB_TO_SRV_MAC

sudo bash ~/scripts/relieve-connection-reuse.sh
