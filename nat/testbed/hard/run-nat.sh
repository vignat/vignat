#!/bin/bash

EXPTIME=$1
MAX_FLOWS=$2

if [ -z $EXPTIME ]; then
    EXPTIME=10
fi

if [ -z $MAX_FLOWS ]; then
    MAX_FLOWS=1024
fi

sudo /nat/build/nat -c 0x01 -n 2 -- -p 0x3 --wan 0 --expire $EXPTIME --max-flows $MAX_FLOWS --starting-port 1025  --extip 10.0.10.53 --eth-dest 0,00:15:c5:ed:7c:9b --eth-dest 1,00:15:c5:ed:89:4a

