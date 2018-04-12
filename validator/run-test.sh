#!/bin/bash

# Setup can be overriden by the $TEST_DIR/config file (especially the $FSPEC_PLUGIN variable)
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
ACTUAL_VF_STDOUT="$UNIQUE_PREFIX.verify.stdout"
DESCRIPTION="git log --follow --diff-filter=A --find-renames=40% $TRACE_FNAME"

function failure (){
    if [ -f "$ACTUAL_OUTCOME" ]; then
        cat "$ACTUAL_OUTCOME"
    fi
    if [ -f "$ACTUAL_VF_STDOUT" ]; then
        cat "$ACTUAL_VF_STDOUT"
    fi
    echo "Test $TEST_NAME FAILED"
    $DESCRIPTION
    exit 1
}

function assert_file_exists (){
    FILE_NAME=$1
    FILE_PURPOSE=$2
    if [ ! -f "$FILE_NAME" ]; then
        echo "Can not find a file serving as $FILE_PURPOSE"
        echo "File $FILE_NAME does not exist"
        failure
    fi
}

. "$TEST_DIR/config"

# Pre-run validation
if [ ! -d $RUN_DIR ]; then
    echo "Directory for the tests $RUN_DIR does not exist"
    exit 1
fi
assert_file_exists $TRACE_FNAME "the test input"
assert_file_exists $FSPEC_PLUGIN "the validator plugin"
assert_file_exists $EXPECTED_OUTCOME "the expected validation outcome"
assert_file_exists $EXPECTED_VF_STDOUT "the expected VeriFast output"

# Run
./validator.byte $FSPEC_PLUGIN $TRACE_FNAME $UNIQUE_PREFIX verifast $SPEC_DIR > $ACTUAL_OUTCOME

# Post-run validation
assert_file_exists $ACTUAL_OUTCOME "the actual validation outcome"
assert_file_exists $ACTUAL_VF_STDOUT "the actual VeriFast output"

# Result check
sed -i "s/$RUN_DIR/<beep>/g" $ACTUAL_VF_STDOUT

OUTCOME_CORRECT=false
cmp --silent $EXPECTED_OUTCOME $ACTUAL_OUTCOME && OUTCOME_CORRECT=true
VF_STDOUT_CORRECT=false
cmp --silent $EXPECTED_VF_STDOUT $ACTUAL_VF_STDOUT && VF_STDOUT_CORRECT=true

if [ $OUTCOME_CORRECT = false ]; then
    echo "Incorrect outcome"
    failure
fi

if [ $VF_STDOUT_CORRECT = false ]; then
    echo "Incorrect verify stdout"
    failure
fi

[ $OUTCOME_CORRECT = true ] && [ $VF_STDOUT_CORRECT = true ]
