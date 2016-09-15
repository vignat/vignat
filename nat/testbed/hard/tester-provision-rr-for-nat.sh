. ./config.sh

echo "sync scripts"
. ./sync-scripts.sh

echo "unbinding $TESTER_PCI_INTERNAL, $TESTER_PCI_EXTERNAL"
$RTE_SDK/tools/dpdk-devbind.py -b igb $TESTER_PCI_INTERNAL $TESTER_PCI_EXTERNAL

echo "start ifaces, configure ip"
ifconfig $TESTER_DEVICE_INTERNAL up
ip addr flush dev $TESTER_DEVICE_INTERNAL
ip addr add $TESTER_IP_INTERNAL/24 dev $TESTER_DEVICE_INTERNAL

echo "configure routes"
ip route flush $SERVER_SUBNET
ip route add $SERVER_SUBNET/24 via $MB_IP_INTERNAL dev $TESTER_DEVICE_INTERNAL
ip route flush cache
arp -s $MB_IP_INTERNAL $MB_INTERNAL_MAC
