#!/bin/bash

# Parameter:
# $1: The script to run pktgen with

if [ -z $1 ]; then
    echo "[pktgen] No script given to start pktgen with"
    exit 1
fi

cd ~/pktgen

sudo ./app/app//x86_64-native-linuxapp-gcc/pktgen -c 0x1ff -n 3 -- -P -m "[1-2:3-4].0, [5-6:7-8].1" -f $1
