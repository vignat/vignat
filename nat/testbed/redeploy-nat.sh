sudo pkill daemon
sudo pkill nat
export RTE_SDK=~/dpdk
cd /nat
rm -r build
make
daemon -r /nat/testbed/run-nat.sh $@
