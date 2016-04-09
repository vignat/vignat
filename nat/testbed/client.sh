sudo apt-get update
sudo apt-get install -y tcpdump hping3
sudo ip route add 192.168.33.0/24 via 192.168.40.2 dev eth1
sudo hping3 192.168.33.10 -k -p 47882 -s 0
