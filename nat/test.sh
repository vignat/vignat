
docker build -t vnds/nat .
docker build -t vnds/client client-docker-img/

docker network create --driver=bridge vnds_int
docker network create --driver=bridge vnds_ext

docker run -itd --name=vnds_c1 --net=vnds_int vnds/client /bin/bash
docker run -itd --name=vnds_c2 --net=vnds_int vnds/client /bin/bash
docker run -itd --name=vnds_s1 --net=vnds_ext vnds/client /bin/bash

# Unfortunately, docker does not have a separate capability to mount a hugetlbfs
docker run -itd --name=vnds_nat --net=vnds_int --privileged vnds/nat /bin/bash
docker network connect vnds_ext vnds_nat

NAT_INT_IP=`docker inspect -f '{{.NetworkSettings.Networks.vnds_int.IPAddress}}' vnds_nat`

docker exec --privileged vnds_c1 ip route del default
docker exec --privileged vnds_c1 ip route add default via $NAT_INT_IP dev eth0
docker exec --privileged vnds_c2 ip route del default
docker exec --privileged vnds_c2 ip route add default via $NAT_INT_IP dev eth0
#docker exec --privileged vnds_s1 ip route del default && ip route add default via 172.17.1.12 dev eth0

docker exec vnds_nat mkdir /mnt/huge
docker exec vnds_nat mount -t hugetlbfs nodev /mnt/huge
docker exec vnds_nat \
       echo 384 > /sys/devices/system/node/node0/hugepages/hugepages-2048kB/nr_hugepages

docker exec -t vnds_nat /root/nat/build/app/nat -c 0x01 -n 2 --vdev=eth_pcap0,iface=eth0 --vdev=eth_pcap1,iface=eth1 -- -p 0x3 wan 1
