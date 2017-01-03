#!/bin/bash
. ./config.sh

# Runs a DPDK app for the specified scenario

# Parameters:
# $1: Scenario, can be "loopback" or "rr"
# $2: Folder of the app; the app must be named "nat"
#     and take the usual arguments e.g. "--extip"
# $3: Additional arguments for the app

if [ $1 != "loopback" -a $1 != "rr" ]; then
    echo "[run] Unknown scenario specified in run-app" 1>&2
    exit 1
fi

if [ -z $2 ]; then
    echo "[run] No app folder specified in run-app" 1>&2
    exit 2
fi


pushd $2 >> /dev/null

echo "[run] Building $1..."
sudo rm build -rf
make

echo "[run] Running $1..."
if [ $1 = "loopback" ]; then
    sudo ./build/nat -c 0x01 -n 2 -- -p 0x3 --wan 0 \
        $3 \
        --extip $MB_IP_EXTERNAL \
        --eth-dest 0,$TESTER_MAC_EXTERNAL --eth-dest 1,$TESTER_MAC_INTERNAL
else
    sudo ./build/nat -c 0x01 -n 2 -- -p 0x7 --wan 2 \
        $3 \
        --extip $MB_IP_TO_SRV \
        --eth-dest 0,$TESTER_MAC_EXTERNAL --eth-dest 1,$TESTER_MAC_INTERNAL --eth-dest 2,$SERVER_MAC
fi

popd >> /dev/null
