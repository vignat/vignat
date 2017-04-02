#!/bin/bash
. ./config.sh

MIDDLEBOX=$1

if [ -z $MIDDLEBOX ]; then
    echo "[bench] No app specified" 1>&2
    exit 1
fi

if [ "$MIDDLEBOX" = "netfilter" ]; then
    echo "no need to kill netfilter"
else
    sudo pkill -9 nat
fi
