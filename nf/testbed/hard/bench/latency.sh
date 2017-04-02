#!/bin/bash
# Latency measurement for multiflow.
# It programs the PktGen server with a number of concurrent flows to be run, runs
# an expriment and collects the results

# Parameter:
# $1: File to write results in


. ~/scripts/config.sh

FLOW_HEATUP=10
EXPIRATION_TIME=10
DURATION=60
REPEAT=1

if [ -z $1 ]; then
    echo "[bench] No result file specified in bench-latency" 1>&2
    exit 1
fi

RESULT_FILE=$1

rm -f $RESULT_FILE
echo "#flows req/s lat_mean(microseconds) lat_stdev" > $RESULT_FILE

echo "[bench] Launching pktgen..."
. ~/scripts/pktgen/run-in-background.sh
sleep 10

echo "[bench] Heating up tables..."
ncons=$(netperf -H $SERVER_HOST -P 0 -t TCP_RR -l $DURATION -- -H "$SERVER_IP" | head -n 1 | awk '{print $6}')
echo "[bench] Heatup reqs/s: $ncons"

echo "[bench] Testing begins..."
for k in $(seq 1 $REPEAT); do
	# maximum is 65535 to ensure no connection ever comes from port 0 on the NAT exterior,
	# which freaks out a lot of software.
	for nflws in 1000 10000 20000 30000 40000 50000 55000 60000 62000 63000 63500 64000 64500 65000 65535; do
		# NOTE: nflws is 1-based while ports are 0-based
		echo "pktgen.dst_port(\"0\", \"max\", $((nflws - 1)))" > ~/cmd.lua
		echo 'pktgen.start("0")' >> ~/cmd.lua
		. ~/scripts/pktgen/send-command.sh ~/cmd.lua

		sleep $FLOW_HEATUP
		# -H $SERVER_HOST: use the server's real name as a side channel for comm with the netperf server
		#                  (i.e. go through the normal network to avoid interference)
		# -t TCP_RR: measure time to do req-resp on TCP, conn setup not included
		# -P 0: don't display the banner or the labels, only results
		# -j: Enable latency statistics
		# -l $DURATION: do testing for $DURATION seconds
		# --
		# -H $SERVER_IP: use the server's IP to do the testing itself
		# -O ...: Select output columns
		#         THROUGHPUT = reqs/s, latency is in microseconds
		stats=$(netperf -H $SERVER_HOST -t TCP_RR -P 0 -j -l $DURATION -- \
				-H "$SERVER_IP" -O THROUGHPUT,MEAN_LATENCY,STDDEV_LATENCY | head -n 1)

		echo "[bench] flows:$nflws (req/s, lat, stdev_lat):($stats)"
		echo "$nflws $stats" >> $RESULT_FILE

		echo 'pktgen.stop("0")' > ~/cmd.lua
		. ~/scripts/pktgen/send-command.sh ~/cmd.lua

		echo "[bench] Waiting for expiration..."
		sleep $EXPIRATION_TIME

                rm ~/cmd.lua
	done
done
