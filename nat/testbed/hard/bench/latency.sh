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

echo "[bench] Launching pktgen..."
. ~/scripts/pktgen/run-in-background.sh

echo "[bench] Heating up tables..."
END_PORT=$(($BEGIN_PORT+$NUM_SAMPLE_FLOWS))
ncons=$(netperf -H $SERVER_HOST -P 0 -t TCP_CC -l $DURATION -- -H "$SERVER_IP   " -p $BEGIN_PORT,$END_PORT | head -n 1 | awk '{print $6}')
echo "[bench] Heatup latency: $ncons"

echo "[bench] Testing begins..."
for k in $(seq 1 $REPEAT); do
	for nflws in 35000 40000 50000 55000; do #1000 10000 25000 35000; do #30000 28000 26000 22000 21000 20000 23000 24000 25000 27000 32000 35000; do # 28000 35000; do #40000 42500 45000 47500 50000; do #1000 5000 10000 15000 20000 25000 33000 40000 50000; do
		BEGIN_PORT=$(($END_PORT + ($RANDOM % 500)))
		END_PORT=$(($BEGIN_PORT+10))
		if [ $MAX_PORT -le $END_PORT ]; then
			BEGIN_PORT=$MIN_PORT
			END_PORT=$(($BEGIN_PORT+10))
		fi
		RANGE_MAX_PORT=$((1000+$nflws))
		echo "pktgen.stop(\"0\")" > cmd.lua
		echo "pktgen.dst_port(\"0\", \"max\", $RANGE_MAX_PORT)" >> cmd.lua
		echo "pktgen.start(\"0\")" >> cmd.lua
		. ~/scripts/pktgen/send-command.sh cmd.lua
		sleep $FLOW_HEATUP
		ncons=$(netperf -H $SERVER_HOST -P 0 -t TCP_RR -l $DURATION -- -H "$SERVER_IP   " -p $BEGIN_PORT,$END_PORT | head -n 1 | awk '{print $6}')
		echo "[bench] $END_PORT - $BEGIN_PORT = $nflws -> $ncons"
		echo $nflws $ncons >> $RESULT_FILE

		echo "pktgen.stop(\"0\")" > cmd.lua
		. ~/scripts/pktgen/send-command.sh cmd.lua

		echo "[bench] Waiting for expiration..."
		sleep $EXPIRATION_TIME

                rm cmd.lua
	done
done
