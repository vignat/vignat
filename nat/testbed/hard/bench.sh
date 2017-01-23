#!/bin/bash
. ./config.sh

# Master script to benchmark VigNAT-related programs.
# Can benchmark different implementations, including non-NATs,
# using different scenarios.

# Parameters:
# $1: The app, either a known name or a DPDK NAT-like app.
#     Known names: "netfilter".
#     Otherwise, a folder name containing a DPDK NAT-like app, e.g. "~/vnds/nat"
# $2: The scenario, one of the following:
#     "loopback": Measure throughput.
#                 Tester and middlebox are connected together in a loop,
#                 using 2 interfaces on each, in different subnets; server is ignored.
#     "1p": Measure throughput.
#           Find the point at which the middlebox starts dropping 1% of packets.
#     "passthrough": Measure latency.
#                    Tester sends packets to server, which pass through the middlebox;
#                    all machines are in the same subnet.
#     "rr": Measure latency.
#           Tester sends packets to server, which are modified by the middlebox;
#           there are two subnets, tester-middlebox and middlebox-server.
#           a.k.a. request/response

if [ -z $1 ]; then
    echo "[bench] No app specified" 1>&2
    exit 1
fi

if [ -z $2 ]; then
    echo "[bench] No scenario specified" 1>&2
    exit 2
fi


# HACK: VigNAT isn't yet verified with 3 interfaces
#       Thus it has to be patched to support it
if [ $1 != "netfilter" ] && [ $2 = "rr" ] && [ -f $1/main.c ]; then
    sed -i -- "s~//{2, 0, 0}~{2, 0, 0}~g" $1/main.c
fi


# Initialize the machines, i.e. software+scripts
. ./init-machines.sh

# Clean first, just in case
. ./clean.sh

# Initialize the network;
# to do that, we need to know which scenario we use, and whether we'll run a DPDK app or not.
NETWORK_SCENARIO=$2
if [ $2 = "1p" ]; then
    NETWORK_SCENARIO="loopback"
fi
NETWORK_APP="dpdk"
if [ $1 = "netfilter" ]; then
    NETWORK_APP="netfilter"
fi
. ./init-network.sh $NETWORK_SCENARIO $NETWORK_APP


CLEAN_APP_NAME=`echo "$1" | tr '/' '_'`
RESULTS_FILE="bench-$CLEAN_APP_NAME-$2.results"
LOG_FILE="bench-$CLEAN_APP_NAME-$2.log"

if [ -f "$RESULTS_FILE" ]; then
    rm "$RESULTS_FILE"
fi

if [ -f "$LOG_FILE" ]; then
    rm "$LOG_FILE"
fi


if [ "$1" = "netfilter" ]; then
    : # Nothing to do, already configured by init-network
else
    echo "[bench] Launching $1..."

    case $2 in
        "1p"|"loopback") SIMPLE_SCENARIO="loopback";;
        "rr"|"passthrough") SIMPLE_SCENARIO="rr";;
    esac

    # Run the app in the background
    # The arguments are not always necessary, but they'll be ignored if unneeded
    (bash ./bench/run-dpdk.sh $SIMPLE_SCENARIO "$1" \
        "--expire 10 --max-flows 65535 --starting-port 1" \
        0<&- &>"$LOG_FILE") &

    # Wait for it to have started
    sleep 20
fi


# Then, run the benchmark depending on the scenario
case $2 in
    "loopback"|"1p")
        LUA_SCRIPT="regular-with-bin-mf"
        if [ $2 = "1p" ]; then
            LUA_SCRIPT="find-breaking-point-mf"
        fi

        echo "[bench] Benchmarking throughput..."
        ssh $TESTER_HOST "bash ~/scripts/pktgen/run.sh ~/scripts/pktgen/$LUA_SCRIPT.lua"
        scp $TESTER_HOST:pktgen/multi-flows.txt "./$RESULTS_FILE"
        ssh $TESTER_HOST "rm pktgen/multi-flows.txt"
        ;;

    "rr"|"passthrough")
        # No difference from a benchmarking point of view, only setup varies

        echo "[bench] Benchmarking latency..."
        ssh $TESTER_HOST "bash ~/scripts/bench/latency.sh ~/bench.results"
        scp $TESTER_HOST:bench.results "./$RESULTS_FILE"
        ssh $TESTER_HOST "rm ~/bench.results"
        ;;

    *)
        echo "[bench] Unknown scenario: $1" 1>&2
        exit 10
        ;;
esac


# HACK: See above HACK
if [ $1 != "netfilter" ] && [ $2 = "rr" ] && [ -f $1/main.c ]; then
    sed -i -- "s~{2, 0, 0}~//{2, 0, 0}~g" $1/main.c
fi


# Leave the machines in a proper state
. ./clean.sh
