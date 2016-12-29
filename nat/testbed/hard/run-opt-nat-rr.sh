#!/bin/bash
# Start our Vigor DPDK-based NAT\beta (optimized)
# configured for the request-responce (ping-pong) scenario.
# The first argument ($1) specifies the directory that contains the expreiment
# config file.
# The second argument ($2) specifies the expiration time for the NAT
# The third argument ($3) - the flow table capacity.


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
sudo pkill -9 $OPT_NAT_SRC_PATH/build/nat
sudo pkill -9 $STUB_SRC_PATH/build/nat

cd $OPT_NAT_SRC_PATH

sudo rm build -rf
make

sudo $OPT_NAT_SRC_PATH/build/nat -c 0x01 -n 2 -- -p 0x7 --wan 2 --expire $EXPTIME --max-flows $MAX_FLOWS --starting-port 1025  --extip $MB_IP_TO_SRV --eth-dest 0,$TESTER_MAC_EXTERNAL --eth-dest 1,$TESTER_MAC_INTERNAL --eth-dest 2,$SERVER_MAC

