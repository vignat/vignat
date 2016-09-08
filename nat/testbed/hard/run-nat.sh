#!/bin/bash

. config.sh

EXPTIME=$1
MAX_FLOWS=$2

if [ -z $EXPTIME ]; then
    EXPTIME=10
fi

if [ -z $MAX_FLOWS ]; then
    MAX_FLOWS=1024
fi

sudo $NAT_SRC_PATH/build/nat -c 0x01 -n 2 -- -p 0x3 --wan 0 --expire $EXPTIME --max-flows $MAX_FLOWS --starting-port 1025  --extip $NAT_IP_EXTERNAL --eth-dest 0,$SERVER_MAC --eth-dest 1,$CLIENT_MAC

