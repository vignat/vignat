
. ~/scripts/config.sh

MIN_PORT=7000
MAX_PORT=65000
BEGIN_PORT=$MIN_PORT
END_PORT=$MIN_PORT

EXPIRATION_TIME=30
DURATION=40

RESULT_FILE=$1

rm -f $RESULT_FILE

for nflws in 10 100 1000 7500 20000; do
	BEGIN_PORT=$END_PORT
	END_PORT=$(($BEGIN_PORT + $nflws))
	if [ $MAX_PORT -le $END_PORT ]; then
		BEGIN_PORT=$MIN_PORT
		END_PORT=$(($BEGIN_PORT + $nflws))
	fi
	ncons=$(netperf -H $SERVER_HOST -P 0 -t TCP_CC -l 30 -- -H "$SERVER_IP   " -p $BEGIN_PORT,$END_PORT | head -n 1 | awk '{print $6}')
	echo "for $nflws you get $ncons"
	echo $nflws $ncons >> $RESULT_FILE
	sleep $EXPIRATION_TIME
done
