#!/bin/bash
# TODO: check all the files for existence
# TODO: on failure, report test description, relevant commit message etc.

# Setup
TEST_NAME=$1
RUN_DIR=$2
TEST_DIR="regression-tests/$TEST_NAME"
TRACE_FNAME="$TEST_DIR/trace"
UNIQUE_PREFIX="$RUN_DIR/$TEST_NAME"
FSPEC_PLUGIN=nat_fspec.cmo
SPEC_DIR="../nf"
EXPECTED_OUTCOME="$TEST_DIR/expected"
EXPECTED_VF_STDOUT="$TEST_DIR/verify.stdout.expected"
ACTUAL_OUTCOME="$UNIQUE_PREFIX.actual_outcome"

. "$TEST_DIR/config"

# Run
./validator.byte $FSPEC_PLUGIN $TRACE_FNAME $UNIQUE_PREFIX verifast $SPEC_DIR > $ACTUAL_OUTCOME

# Check
ACTUAL_VF_STDOUT="$UNIQUE_PREFIX.verify.stdout"

sed -i "s/$RUN_DIR/<beep>/g" $ACTUAL_VF_STDOUT

OUTCOME_CORRECT=false
cmp --silent $EXPECTED_OUTCOME $ACTUAL_OUTCOME && OUTCOME_CORRECT=true
VF_STDOUT_CORRECT=false
cmp --silent $EXPECTED_VF_STDOUT $ACTUAL_VF_STDOUT && VF_STDOUT_CORRECT=true

if [ $OUTCOME_CORRECT = false ]; then
    echo "Incorrect outcome"
fi

if [ $VF_STDOUT_CORRECT = false ]; then
    echo "Incorrect verify stdout"
fi

[ $OUTCOME_CORRECT = true ] && [ $VF_STDOUT_CORRECT = true ]
