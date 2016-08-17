NAT_INTERNAL_MAC=00:1e:67:92:29:6d
ifconfig em2 up
ip addr add 192.168.0.5/24 dev em2
ifconfig em3 up
ip addr add 192.168.3.5/24 dev em3
ip route add 192.168.2.0/24 via 192.168.3.2 dev em3
arp -s 192.168.3.2 $NAT_INTERNAL_MAC
#hping3 192.168.33.10 -k -p 47882 -s 0
