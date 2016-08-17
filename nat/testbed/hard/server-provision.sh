NAT_EXTERNAL_MAC=00:1e:67:92:29:6c
ifconfig em2 up
ip addr add 192.168.2.10/24 dev em2
ifconfig em3 up
ip addr add 192.168.0.10/24 dev em3
arp -s 192.168.2.2 $NAT_EXTERNAL_MAC
#hping3 192.168.33.10 -k -p 47882 -s 0
