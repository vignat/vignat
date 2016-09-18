#!/bin/bash

CONFIG_PATH=$1

if [ -z $CONFIG_PATH ]; then
    CONFIG_PATH=.
fi

. $CONFIG_PATH/config.sh

EXPTIME=$2
MAX_FLOWS=$3

if [ -z $EXPTIME ]; then
    EXPTIME=1
fi

if [ -z $MAX_FLOWS ]; then
    MAX_FLOWS=30000
fi

sudo pkill -9 $NAT_SRC_PATH/build/nat
sudo pkill -9 $STUB_SRC_PATH/build/nat

cd $NAT_SRC_PATH

sudo rm build -rf
make


sudo $NAT_SRC_PATH/build/nat -c 0x01 -n 2 -- -p 0x3 --wan 0 --expire $EXPTIME --max-flows $MAX_FLOWS --starting-port 1025  --extip $MB_IP_EXTERNAL --eth-dest 0,$TESTER_MAC_EXTERNAL --eth-dest 1,$TESTER_MAC_INTERNAL

