#!/bin/bash
. ./config.sh

# Master script to initialize VigNAT-related programs benchmarks.
# Can work with different implementations, including non-NATs,
# using different scenarios.

# Parameters:
# $1: The app, either a known name or a DPDK NAT-like app.
#     Known names: "netfilter".
#     Otherwise, a folder name containing a DPDK NAT-like app, e.g. "~/vnds/nat"
# $2: The scenario, one of the following:
#     "mg-1p": Measure throughput: find the rate at which the middlebox
#              starts loosing 1% of packets.
#     "mg-existing-flows-latency": Measure the forwarding latency for existing
#                                  flows.
#     "mg-new-flows-latency": Measure the forwarding latency for new flows.
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

MIDDLEBOX=$1
SCENARIO=$2

if [ -z $MIDDLEBOX ]; then
    echo "[bench] No app specified" 1>&2
    exit 1
fi

if [ -z $SCENARIO ]; then
    echo "[bench] No scenario specified" 1>&2
    exit 2
fi


# Initialize the network;
# to do that, we need to know which scenario we use, and whether we'll run a DPDK app or not.
NETWORK_SCENARIO=$SCENARIO
case $SCENARIO in
    "1p"|"loopback"|"mg-1p"|"mg-existing-flows-latency"|"mg-new-flows-latency")
        NETWORK_SCENARIO="loopback"
        ;;
    "passthrough")
        NETWORK_SCENARIO="passthrough"
        ;;
    "rr")
        NETWORK_SCENARIO="rr"
        ;;
    *)
        echo "unknown scenario $SCENARIO" 1>&2
        exit 10
esac

NETWORK_APP="dpdk"
if [ $MIDDLEBOX = "netfilter" ]; then
    NETWORK_APP="netfilter"
elif [ ! -d $MIDDLEBOX ]; then
    echo "Unknown middlebox app: $MIDDLEBOX" 1>&2
    exit 10
fi

. ./init-network.sh $NETWORK_SCENARIO $NETWORK_APP


CLEAN_APP_NAME=`echo "$MIDDLEBOX" | tr '/' '_'`
LOG_FILE="bench-$CLEAN_APP_NAME-$SCENARIO-init.log"

if [ -f "$LOG_FILE" ]; then
    rm "$LOG_FILE"
fi


if [ "$MIDDLEBOX" = "netfilter" ]; then
    case $SCENARIO in
	"mg-new-flows-latency")
	    EXPIRATION_TIME=2
	    ;;
        "1p"|"loopback"|"mg-1p"|"mg-existing-flows-latency"|"rr"|"passthrough")
            EXPIRATION_TIME=60
            ;;
    esac

    bash ./util/netfilter-short-timeout.sh $EXPIRATION_TIME
else
    echo "[bench] Launching $MIDDLEBOX..."

    EXPIRATION_TIME=60

    case $SCENARIO in
        "mg-new-flows-latency")
            SIMPLE_SCENARIO="loopback"
            EXPIRATION_TIME=2
            ;;
        "1p"|"loopback"|"mg-1p"|"mg-existing-flows-latency")
            SIMPLE_SCENARIO="loopback"
            EXPIRATION_TIME=60
            ;;
        "rr"|"passthrough")
            SIMPLE_SCENARIO="rr"
            EXPIRATION_TIME=60
            ;;
        *)
            echo "Unknown scenario $SCENARIO" 1>&2
            exit 10
            ;;
    esac

    # Run the app in the background
    # The arguments are not always necessary, but they'll be ignored if unneeded
    (bash ./bench/run-dpdk.sh $SIMPLE_SCENARIO "$MIDDLEBOX" \
        "--expire $EXPIRATION_TIME --max-flows 65535 --starting-port 1" \
        0<&- &>"$LOG_FILE") &

    # Wait for it to have started
    sleep 20
fi
