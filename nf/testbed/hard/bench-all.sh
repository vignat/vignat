#!/bin/bash

# Initialize the machines, i.e. software+scripts
. ./init-machines.sh
# Clean first, just in case
. ./clean.sh

VNDS_PREFIX="$HOME/vnds/nf"

NOW=$(date +"%d.%m.%Y_%H_%M")

MIDDLEBOXES=("$VNDS_PREFIX/vignat" "$VNDS_PREFIX/unverified-nat" "$VNDS_PREFIX/nop")
SCENARIOS=("mg-new-flows-latency" "mg-existing-flows-latency" "mg-1p")

mkdir -p $NOW

for MIDDLEBOX in ${MIDDLEBOXES[@]}; do
    # The second parameter should not matter (it doesn't for mg-* scenarios,
    # but unfortunately it does for the old ones, so to not try this for those)
    . ./init.sh $MIDDLEBOX "mg-1p"
    for SCENARIO in ${SCENARIOS[@]}; do
        . ./start-middlebox.sh $MIDDLEBOX $SCENARIO
        CLEAN_APP_NAME=`echo "$MIDDLEBOX" | tr '/' '_'`
        RESULTS_FILE="$NOW/$CLEAN_APP_NAME-$SCENARIO.results"
        . ./run.sh $MIDDLEBOX $SCENARIO $RESULTS_FILE
        . ./stop-middlebox.sh $MIDDLEBOX $SCENARIO
    done
done

. ./clean.sh
