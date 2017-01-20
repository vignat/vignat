#!/bin/bash
# Latency measurement for multiflow.
# It programs the PktGen server with a number of concurrent flows to be run, runs
# an expriment and collects the results

# Parameter:
# $1: File to write results in


. ~/scripts/config.sh

MIN_PORT=52000
MAX_PORT=60000
BEGIN_PORT=MIN_PORT
END_PORT=MIN_PORT
NUM_SAMPLE_FLOWS=10
FLOW_HEATUP=50
EXPIRATION_TIME=30
DURATION=10
REPEAT=3

if [ -z $1 ]; then
    echo "[bench] No result file specified in bench-latency" 1>&2
    exit 1
fi

RESULT_FILE=$1

rm -f $RESULT_FILE
echo "#flows req/s one-way-lat" > $RESULT_FILE

echo "[bench] Launching pktgen..."
. ~/scripts/pktgen/run-in-background.sh

echo "[bench] Heating up tables..."
END_PORT=$(($BEGIN_PORT+$NUM_SAMPLE_FLOWS))
ncons=$(netperf -H $SERVER_HOST -P 0 -t TCP_CC -l $DURATION -- -H "$SERVER_IP   " -p $BEGIN_PORT,$END_PORT | head -n 1 | awk '{print $6}')
echo "[bench] Heatup reqs/s: $ncons"

echo "[bench] Testing begins..."
for k in $(seq 1 $REPEAT); do
	for nflws in 1000 10000 20000 30000 35000 40000 45000 50000 55000 60000 60500 61000 61500 62000 62500 63000 63500 64000 64500 65000 65536; do
		BEGIN_PORT=$(($END_PORT + ($RANDOM % 500)))
		END_PORT=$(($BEGIN_PORT+10))
		if [ $MAX_PORT -le $END_PORT ]; then
			BEGIN_PORT=$MIN_PORT
			END_PORT=$(($BEGIN_PORT+10))
		fi
		RANGE_MAX_PORT=$((1000+$nflws))
		echo 'pktgen.stop("0")' > cmd.lua
		echo "pktgen.dst_port(\"0\", \"max\", $RANGE_MAX_PORT)" >> cmd.lua
		echo 'pktgen.start("0")' >> cmd.lua
		. ~/scripts/pktgen/send-command.sh cmd.lua
		sleep $FLOW_HEATUP
		ncons=$(netperf -H $SERVER_HOST -P 0 -t TCP_RR -l $DURATION -- -H "$SERVER_IP" -p $BEGIN_PORT,$END_PORT | head -n 1 | awk '{print $6}')

                # lat = 1/(req/s); one-way lat = lat/2; in milliseconds, *1000
                lat=`bc -l <<< "scale=3; (1000 / $ncons) / 2"`
		echo "[bench] begin:$BEGIN_PORT end:$END_PORT flows:$nflws req/s:$ncons lat:$lat"
		echo $nflws $ncons $lat >> $RESULT_FILE

		echo 'pktgen.stop("0")' > cmd.lua
		. ~/scripts/pktgen/send-command.sh cmd.lua

		echo "[bench] Waiting for expiration..."
		sleep $EXPIRATION_TIME

                rm cmd.lua
	done
done
