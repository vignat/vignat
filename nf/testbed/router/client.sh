sudo apt-get update
sudo apt-get install -y tcpdump hping3 python-scapy wget
sudo ip route add 192.168.34.0/24 via 192.168.41.2 dev eth1
sudo arp -s 192.168.41.2 08:00:27:00:44:72
#sudo hping3 192.168.33.10 -k -p 47882 -s 0
