#!/bin/bash
. ./config.sh

# Initializes the network for the specified scenario and app,
# by running the appropriate scripts on all three machines.

# Parameters:
# $1: Scenario; there must exist a folder "init-network-$1",
#     with a "tester.sh" script and optionally a "server.sh" script
# $2: App; there must exist a folder "init-network-$1/$2",
#     with a "middlebox.sh" script.


if [ -z $1 ]; then
    echo "[init] Error, no scenario specified in init-network" 1>&2
    exit 1
fi

if [ ! -d ./init-network-$1 ]; then
    echo "[init] Error, unknown scenario specified in init-network" 1>&2
    exit 2
fi

if [ -z $2 ]; then
    echo "[init] Error, no app specified in init-network" 1>&2
    exit 3
fi

if [ ! -d ./init-network-$1/$2 ]; then
    echo "[init] Error, unknown app specified in init-network" 1>&2
    exit 4
fi


if [ -f ./init-network-$1/server.sh ]; then
    ssh $SERVER_HOST "bash ~/scripts/init-network-$1/server.sh"
fi

ssh $TESTER_HOST "bash ~/scripts/init-network-$1/tester.sh"

. ./init-network-$1/$2/middlebox.sh
