#!/bin/bash

CONFIG_PATH=$1

if [ -z $CONFIG_PATH ]; then
    CONFIG_PATH=.
fi

. $CONFIG_PATH/config.sh

sudo pkill -9 $NAT_SRC_PATH/build/nat
sudo pkill -9 $OPT_NAT_SRC_PATH/build/nat
sudo pkill -9 $STUB_SRC_PATH/build/nat

cd $STUB_SRC_PATH

sudo rm build -rf
make

sudo $STUB_SRC_PATH/build/nat -c 0x01 -n 2 -b $TESTER_PCI_EXTERNAL -- -p 0x3 --wan 1 --extip $MB_IP_TO_SRV --eth-dest 0,$TESTER_MAC_INTERNAL --eth-dest 1,$SERVER_MAC

