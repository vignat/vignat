sudo apt-get update
sudo apt-get install -y tcpdump git wget build-essential libpcap-dev linux-headers-3.13.0-35 libglib2.0-dev

wget http://dpdk.org/browse/dpdk/snapshot/dpdk-2.2.0.tar.gz -O dpdk.tar.gz
tar xf dpdk.tar.gz
mv dpdk-* dpdk
rm dpdk.tar.gz

cd dpdk && sed -ri 's,(PMD_PCAP=).*,\1y,' config/common_linuxapp && make config install -j2 T=x86_64-native-linuxapp-gcc

export RTE_SDK=~/dpdk
export RTE_TARGET=x86_64-native-linuxapp-gcc

cd ~/

git clone --depth 1 git://github.com/necto/vnds
chmod -R 777 vnds

cd vnds/nat

make
