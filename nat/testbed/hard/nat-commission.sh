#!/bin/bash
# Commission the middlebox to prepare it to run various NATs,
# especially DPDK-based ones.
pushd $HOME

sudo apt-get update
KERNEL_RELEASE=$(uname -r)
sudo apt-get install -y tcpdump git wget build-essential libpcap-dev linux-headers-3.13.0-93 linux-headers-$KERNEL_RELEASE libglib2.0-dev daemon iperf3 netperf tmux

wget http://fast.dpdk.org/rel/dpdk-16.07.tar.xz -O dpdk.tar.xz
tar xf dpdk.tar.xz
mv -T dpdk-* dpdk
rm dpdk.tar.xz

cd dpdk
sed -ri 's,(PMD_PCAP=).*,\1y,' config/common_linuxapp
make config T=x86_64-native-linuxapp-gcc
make install -j T=x86_64-native-linuxapp-gcc DESTDIR=.

export RTE_SDK=$HOME/dpdk
export RTE_TARGET=x86_64-native-linuxapp-gcc

popd
