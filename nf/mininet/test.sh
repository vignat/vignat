
docker build -t vnds/nat .
docker build -t vnds/client client-docker-img/

docker network create --driver=bridge --subnet=192.168.10.0/24 vnds_int
docker network create --driver=bridge --subnet=192.168.11.0/24 vnds_ext

docker run -itd --name=vnds_c1 --net=vnds_int vnds/client /bin/bash
docker run -itd --name=vnds_c2 --net=vnds_int vnds/client /bin/bash
docker run -itd --name=vnds_s1 --net=vnds_ext vnds/client /bin/bash

# Unfortunately, docker does not have a separate capability to mount a hugetlbfs
docker run -itd --name=vnds_nat --net=vnds_int --privileged vnds/nat /bin/bash
docker network connect vnds_ext vnds_nat

S1_IP=`docker inspect -f '{{.NetworkSettings.Networks.vnds_ext.IPAddress}}' vnds_s1`
NAT_INT_IP=`docker inspect -f '{{.NetworkSettings.Networks.vnds_int.IPAddress}}' vnds_nat`
NAT_EXT_IP=`docker inspect -f '{{.NetworkSettings.Networks.vnds_ext.IPAddress}}' vnds_nat`
NAT_INT_GATEWAY_IP=`docker inspect -f '{{.NetworkSettings.Networks.vnds_int.Gateway}}' vnds_nat`
NAT_EXT_GATEWAY_IP=`docker inspect -f '{{.NetworkSettings.Networks.vnds_ext.Gateway}}' vnds_nat`

docker exec vnds_nat ping $NAT_INT_GATEWAY_IP -c 1
docker exec vnds_nat ping $NAT_EXT_GATEWAY_IP -c 1

NAT_INT_GATEWAY_MAC=`docker exec vnds_nat sh -c "arp -n $NAT_INT_GATEWAY_IP | awk 'NR==2{print \\\$3;}'"` 
NAT_EXT_GATEWAY_MAC=`docker exec vnds_nat sh -c "arp -n $NAT_EXT_GATEWAY_IP | awk 'NR==2{print \\\$3;}'"` 

docker exec --privileged vnds_c1 ip route del default
docker exec --privileged vnds_c1 ip route add default via $NAT_INT_IP dev eth0
docker exec --privileged vnds_c2 ip route del default
docker exec --privileged vnds_c2 ip route add default via $NAT_INT_IP dev eth0
#docker exec --privileged vnds_s1 ip route del default && ip route add default via 172.17.1.12 dev eth0

docker exec vnds_nat mkdir /mnt/huge
docker exec vnds_nat mount -t hugetlbfs nodev /mnt/huge
docker exec vnds_nat sh -c 'echo 384 > /sys/devices/system/node/node0/hugepages/hugepages-2048kB/nr_hugepages'

docker exec -t vnds_nat /root/nat/build/app/nat -c 0x01 -n 2 --vdev=eth_pcap0,iface=eth0 --vdev=eth_pcap1,iface=eth1 -- -p 0x3 --wan 1 --extip $NAT_EXT_IP --eth-dest 0,$NAT_INT_GATEWAY_MAC --eth-dest 1,$NAT_EXT_GATEWAY_MAC

#docker exec -it vnds_c1 hping3 $S1_IP -k -p 47882 -s 0

# hping3 172.19.0.2 -k -p 47882 -s 0
