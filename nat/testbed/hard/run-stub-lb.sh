#!/bin/bash

CONFIG_PATH=$1

if [ -z $CONFIG_PATH ]; then
    CONFIG_PATH=.
fi

CONFIG_PATH=/home/necto/vnds/nat/testbed/hard

. $CONFIG_PATH/config.sh

sudo pkill -9 $NAT_SRC_PATH/build/nat
sudo pkill -9 $OPT_NAT_SRC_PATH/build/nat
sudo pkill -9 $STUB_SRC_PATH/build/nat

cd $STUB_SRC_PATH

sudo rm build -rf
make

sudo $STUB_SRC_PATH/build/nat -c 0x01 -n 2 -- -p 0x3 --wan 0 --extip $MB_IP_EXTERNAL --eth-dest 0,$TESTER_MAC_EXTERNAL --eth-dest 1,$TESTER_MAC_INTERNAL

