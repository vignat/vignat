sudo apt-get update
KERNEL_RELEASE=$(uname -r)
sudo apt-get install -y tcpdump hping3 python-scapy git wget build-essential libpcap-dev linux-headers-$KERNEL_RELEASE libglib2.0-dev daemon iperf3 netperf liblua5.3-dev

wget http://fast.dpdk.org/rel/dpdk-16.07.tar.xz -O dpdk.tar.xz
tar xf dpdk.tar.xz
mv dpdk-* dpdk
rm dpdk.tar.gz

cd dpdk
sed -ri 's,(PMD_PCAP=).*,\1y,' config/common_linuxapp
make config T=x86_64-native-linuxapp-gcc
make install -j T=x86_64-native-linuxapp-gcc DESTDIR=.

export RTE_SDK=/home/necto/dpdk
export RTE_TARGET=x86_64-native-linuxapp-gcc

cd ~
wget http://dpdk.org/browse/apps/pktgen-dpdk/snapshot/pktgen-3.0.13.tar.gz -O pktgen.tar.gz
tar xf pktgen
mv pktgen-* pktgen
rm pktgen.tar.gz

cd pktgen
make -j
