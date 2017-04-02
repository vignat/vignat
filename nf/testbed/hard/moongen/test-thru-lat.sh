#!/bin/bash

RESULT_FILE=results.txt
MOONGEN_PATH=$HOME/moon-gen
PAUSE=60

rm -f $RESULT_FILE

touch $RESULT_FILE
for flows in 1 10 100 1000 10000 20000 30000 40000 50000 60000 65000 65534; do
	echo "sudo $MOONGEN_PATH/build/MoonGen ~/scripts/moongen/l3-load-latency.lua 1 0 --flows $flows $@"
	sudo $MOONGEN_PATH/build/MoonGen ~/scripts/moongen/l3-load-latency.lua 1 0 --flows $flows $@
	echo -n "$flows " >> $RESULT_FILE
	awk -F, '{print $4}' txpkts.csv  | tail -n 2 | head -n 1 | xargs echo -n >> $RESULT_FILE
	echo -n " " >> $RESULT_FILE
	awk -F, '{print $4}' rxpkts.csv  | tail -n 2 | head -n 1 | xargs echo -n >> $RESULT_FILE
	echo -n " " >> $RESULT_FILE
	awk -F, '{sqsum += ($1*$1)*$2; total += $1*$2; cnt += $2} END {print total/cnt " " sqrt(sqsum/cnt - total*total/cnt/cnt) }' latency-histogram.csv | xargs echo -n >> $RESULT_FILE
	echo "" >> $RESULT_FILE
	sleep $PAUSE
done

