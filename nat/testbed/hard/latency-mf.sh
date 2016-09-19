
. ~/scripts/config.sh

MIN_PORT=59000
MAX_PORT=63000
BEGIN_PORT=MIN_PORT
END_PORT=MAX_PORT
FLOW_HEATUP=50
EXPIRATION_TIME=15
DURATION=50
REPEAT=7

RESULT_FILE=$1

rm -f $RESULT_FILE

echo "[latMF] testing begins"
for k in $(seq 1 $REPEAT); do	
	for nflws in 100 1000 5000 7500 10000 15000 20000 25000 33000 40000 50000; do
		BEGIN_PORT=$END_PORT
		END_PORT=$(($BEGIN_PORT+10))
		if [ $MAX_PORT -le $END_PORT ]; then
			BEGIN_PORT=$MIN_PORT
			END_PORT=$(($BEGIN_PORT+10))
		fi
		RANGE_MAX_PORT=$((1000+$nflws))
		echo "pktgen.stop(\"0\")" > cmd.lua
		echo "pktgen.delay(\"1000\")" >> cmd.lua
		echo "pktgen.dst_port(\"0\", \"max\", $RANGE_MAX_PORT)" >> cmd.lua
		echo "pktgen.delay(\"1000\")" >> cmd.lua
		echo "pktgen.start(\"0\")" >> cmd.lua
		. ~/scripts/cmd-pktgen-serv.sh cmd.lua
		sleep $FLOW_HEATUP
		ncons=$(netperf -H $SERVER_HOST -P 0 -t TCP_CC -l $DURATION -- -H "$SERVER_IP   " -p $BEGIN_PORT,$END_PORT | head -n 1 | awk '{print $6}')
		echo "for $nflws you get $ncons"
		echo $nflws $ncons >> $RESULT_FILE
		sleep $EXPIRATION_TIME
	done
done
echo "[latMF] testing finished"
