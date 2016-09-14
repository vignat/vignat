#!/bin/bash

CONFIG_PATH=$1

if [ -z $CONFIG_PATH ]; then
    CONFIG_PATH=.
fi

CONFIG_PATH=/home/necto/vnds/nat/testbed/hard

. $CONFIG_PATH/config.sh

sudo $STUB_SRC_PATH/build/nat -c 0x01 -n 2 -- -p 0x3 --wan 0 --extip $NAT_IP_EXTERNAL --eth-dest 0,00:1e:67:92:2a:bc --eth-dest 1,00:1e:67:92:2a:bd

