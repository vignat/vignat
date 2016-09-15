#!/bin/bash

CONFIG_PATH=$1

if [ -z $CONFIG_PATH ]; then
    CONFIG_PATH=.
fi

CONFIG_PATH=/home/necto/vnds/nat/testbed/hard

. $CONFIG_PATH/config.sh

sudo $STUB_SRC_PATH/build/nat -c 0x01 -n 2 -- -p 0x3 --wan 1 --extip $MB_IP_TO_SRV --eth-dest 0,$TESTER_MAC_INTERNAL --eth-dest 1,$SERVER_MAC

