
. ./config.sh
. ./dpdk-setup-middlebox.sh

sudo pkill -9 $NAT_SRC_PATH/build/nat
sudo pkill -9 $STUB_SRC_PATH/build/nat

cd $NAT_SRC_PATH

sudo rm build -rf
make

