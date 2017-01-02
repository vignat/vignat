#!/bin/bash
# Latency measurement for multiflow.
# The scripts expects PktGen server to be running and listening on port 22022
# It programs the PktGen server with a number of concurrent flows to be run, runs
# an expriment and collects the results in the
# file provided as the first argument $1

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

RESULT_FILE=$1

rm -f $RESULT_FILE

echo "[latMF] heat up tables"
END_PORT=$(($BEGIN_PORT+$NUM_SAMPLE_FLOWS))
ncons=$(netperf -H $SERVER_HOST -P 0 -t TCP_CC -l $DURATION -- -H "$SERVER_IP   " -p $BEGIN_PORT,$END_PORT | head -n 1 | awk '{print $6}')
echo "[latMF] heatup latency: $ncons"

echo "[latMF] testing begins"
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
		. ~/scripts/cmd-pktgen-serv.sh cmd.lua
		sleep $FLOW_HEATUP
		ncons=$(netperf -H $SERVER_HOST -P 0 -t TCP_RR -l $DURATION -- -H "$SERVER_IP   " -p $BEGIN_PORT,$END_PORT | head -n 1 | awk '{print $6}')
		echo "[latMF]for $END_PORT - $BEGIN_PORT = $nflws you get $ncons"
		echo $nflws $ncons >> $RESULT_FILE

		echo "pktgen.stop(\"0\")" > cmd.lua
		. ~/scripts/cmd-pktgen-serv.sh cmd.lua
		
		echo "[latMF] stopped, waiting for expiration."
		sleep $EXPIRATION_TIME
	done
done
echo "[latMF] testing finished"
