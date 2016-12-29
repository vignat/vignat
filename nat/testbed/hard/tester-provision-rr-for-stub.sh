# Configure the tester for the request-response (ping-pong) scenario
# with middlebox running a no-op plain forwarding applicaiton.
. ~/scripts/config.sh

. ~/scripts/dpdk-setup-tester-rr.sh

echo "unbinding $TESTER_PCI_INTERNAL"
$RTE_SDK/tools/dpdk-devbind.py -b igb $TESTER_PCI_INTERNAL

echo "waiting for it to happen"
sleep 8

echo "start ifaces, configure ip"
ifconfig $TESTER_DEVICE_EXTERNAL down
ifconfig $TESTER_DEVICE_INTERNAL up
ip addr flush dev $TESTER_DEVICE_INTERNAL
ip addr add $TESTER_IP_FOR_STUB/24 dev $TESTER_DEVICE_INTERNAL

echo "configure routes"
ip route flush $SERVER_SUBNET
ip route flush cache
arp -s $SERVER_IP $MB_INTERNAL_MAC

sudo bash ~/scripts/relieve-connection-reuse.sh
echo "configured"
