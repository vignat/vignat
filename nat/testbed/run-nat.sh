#!/bin/bash

EXPTIME=$1
MAX_FLOWS=$2

if [ -z $EXPTIME ]; then
    EXPTIME=10
fi

if [ -z $MAX_FLOWS ]; then
    MAX_FLOWS=1024
fi

sudo /nat/build/nat -c 0x01 -n 2 -- -p 0x3 --wan 0 --expire $EXPTIME --max-flows $MAX_FLOWS --starting-port 1025  --extip 192.168.33.2 --eth-dest 0,08:00:27:53:8b:38 --eth-dest 1,08:00:27:c1:13:47

