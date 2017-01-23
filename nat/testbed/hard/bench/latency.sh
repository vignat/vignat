#!/bin/bash
# Latency measurement for multiflow.
# It programs the PktGen server with a number of concurrent flows to be run, runs
# an expriment and collects the results

# Parameter:
# $1: File to write results in


. ~/scripts/config.sh

FLOW_HEATUP=20
EXPIRATION_TIME=20
DURATION=10
REPEAT=1

if [ -z $1 ]; then
    echo "[bench] No result file specified in bench-latency" 1>&2
    exit 1
fi

RESULT_FILE=$1

rm -f $RESULT_FILE
echo "#flows req/s one-way-lat" > $RESULT_FILE

echo "[bench] Launching pktgen..."
. ~/scripts/pktgen/run-in-background.sh
sleep 10

echo "[bench] Heating up tables..."
ncons=$(netperf -H $SERVER_HOST -P 0 -t UDP_RR -l $DURATION -- -H "$SERVER_IP" | head -n 1 | awk '{print $6}')
echo "[bench] Heatup reqs/s: $ncons"

echo "[bench] Testing begins..."
for k in $(seq 1 $REPEAT); do
	# maximum is 65535 to ensure no connection ever comes from port 0 on the NAT exterior,
	# which freaks out a lot of software.
	for nflws in 1000 10000 20000 30000 35000 40000 45000 50000 55000 60000 61000; do
		# NOTE: nflws is 1-based while ports are 0-based
		echo "pktgen.dst_port(\"0\", \"max\", $((nflws - 1)))" > ~/cmd.lua
		echo 'pktgen.start("0")' >> ~/cmd.lua
		. ~/scripts/pktgen/send-command.sh ~/cmd.lua

		sleep $FLOW_HEATUP
		ncons=$(netperf -H $SERVER_HOST -P 0 -t UDP_RR -l $DURATION -- -H "$SERVER_IP" | head -n 1 | awk '{print $6}')

                # lat = 1/(req/s); one-way lat = lat/2; in milliseconds, *1000
                lat=`bc -l <<< "scale=3; (1000 / $ncons) / 2"`
		echo "[bench] begin:$BEGIN_PORT end:$END_PORT flows:$nflws req/s:$ncons lat:$lat"
		echo $nflws $ncons $lat >> $RESULT_FILE

		echo 'pktgen.stop("0")' > ~/cmd.lua
		. ~/scripts/pktgen/send-command.sh ~/cmd.lua

		echo "[bench] Waiting for expiration..."
		sleep $EXPIRATION_TIME

                rm ~/cmd.lua
	done
done
