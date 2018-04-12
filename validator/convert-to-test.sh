#!/bin/bash

PREFIX=$1
TEST_NAME=$2
PLUGIN=$3

if [ "$PREFIX" = "" ]; then
    echo "Please specify the trace prefix."
    echo "The trace prefix should be in the form: aaa/000032"
    echo "There must exist files:"
    echo "  <prefix>.src - trace source"
    echo "  <prefix>.validator_result - trace validation outcome"
    echo "  <prefix>.verify.stdout - VeriFast output log"
    read -p '>' PREFIX
fi

if [ "$TEST_NAME" = "" ]; then
    echo "Please specify the test name."
    echo "The test name must be different from other tests in regression-tests/"
    read -p '>' TEST_NAME
fi

if [ "$PLUGIN" = "" ]; then
    echo "Please specify the validator plugin name."
    read -p '>' PLUGIN
fi

echo "Adding the trace $PREFIX.src as a regression "
echo "test $TEST_NAME using $PLUGIN."
echo "Please do not forget to write a decent commit"
echo "message as it will serve as the test description."

TEST_DIR="regression-tests/$TEST_NAME"

function assert_file_exists (){
    FILE_NAME=$1
    FILE_PURPOSE=$2
    if [ ! -f "$FILE_NAME" ]; then
        echo "Can not find a file serving as $FILE_PURPOSE"
        echo "File $FILE_NAME does not exist"
        exit 1
    fi
}

if [ -d $TEST_DIR ]; then
    echo "Directory $TEST_DIR already exists."
    echo "Please choose a different name for the test."
    exit 1
fi
assert_file_exists "$PREFIX.src" "the test trace"
assert_file_exists "$PREFIX.validator_result" "the validator result"
assert_file_exists "$PREFIX.verify.stdout" "the VeriFast result"
assert_file_exists "$PLUGIN" "the validator plugin"

mkdir "$TEST_DIR"
cp "$PREFIX.src" "$TEST_DIR/trace"
cp "$PREFIX.validator_result" "$TEST_DIR/expected"
cp "$PREFIX.verify.stdout" "$TEST_DIR/verify.stdout.expected"
echo "FSPEC_PLUGIN=$PLUGIN" > "$TEST_DIR/config"

# Canonicalize the file name in the VeriFast report.
sed -i "s:$PREFIX:<beep>/$TEST_NAME:g" "$TEST_DIR/verify.stdout.expected"

git add "$TEST_DIR"
