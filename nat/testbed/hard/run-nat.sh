#!/bin/bash

CLIENT_MAC=00:1e:67:92:2a:bd
SERVER_MAC=00:1e:67:92:2a:29
NAT_EXTIP=192.168.2.2

EXPTIME=$1
MAX_FLOWS=$2

if [ -z $EXPTIME ]; then
    EXPTIME=10
fi

if [ -z $MAX_FLOWS ]; then
    MAX_FLOWS=1024
fi

sudo /nat/build/nat -c 0x01 -n 2 -- -p 0x3 --wan 0 --expire $EXPTIME --max-flows $MAX_FLOWS --starting-port 1025  --extip $NAT_EXTIP --eth-dest 0,$SERVER_MAC --eth-dest 1,$CLIENT_MAC

