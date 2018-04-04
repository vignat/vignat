sudo apt-get update && sudo apt-get install -y hping3

sudo ip route add 10.0.0.0/16 via 10.9.0.2 dev eth1
sudo arp -s 10.2.0.0 00:00:00:00:02:00
