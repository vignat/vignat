sudo apt-get update
sudo apt-get install -y tcpdump git wget build-essential libpcap-dev linux-headers-3.13.0-86 linux-headers-3.13.0-86-generic libglib2.0-dev daemon

wget http://dpdk.org/browse/dpdk/snapshot/dpdk-2.2.0.tar.gz -O dpdk.tar.gz
tar xf dpdk.tar.gz
mv dpdk-* dpdk
rm dpdk.tar.gz

cd dpdk
sed -ri 's,(PMD_PCAP=).*,\1y,' config/common_linuxapp
make config T=x86_64-native-linuxapp-gcc
make install -j2 T=x86_64-native-linuxapp-gcc DESTDIR=.

export RTE_SDK=/home/vagrant/dpdk
export RTE_TARGET=x86_64-native-linuxapp-gcc

. /nat/testbed/redeploy-nat.sh

daemon -r /nat/testbed/run-nat.sh
