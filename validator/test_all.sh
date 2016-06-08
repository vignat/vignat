#!/bin/bash
if [ -z $VERIFAST ]; then VERIFAST="verifast"; fi
KLEE_OUT_DIR=$1
WORK_DIR=$2
SINGLE_TEST=$3
REPORT_FNAME="${WORK_DIR}/report.txt"
SPEC_DIR="../nat"

analyze_result() {
    RESULT=$1
    FNAME=$2
    if grep -q "0 errors found" $RESULT; then
        echo $FNAME success >> $REPORT_FNAME
    else
        if grep -q "Assertion might not hold" $RESULT; then
            echo $FNAME assertion fail >> $REPORT_FNAME
        fi
        if grep -q "No matching heap chunks" $RESULT; then
            echo $FNAME nochunks fail >> $REPORT_FNAME
        fi
        if grep -q "Function leaks heap chunks" $RESULT; then
            echo $FNAME leak fail >> $REPORT_FNAME
        fi
        if grep -q "Cannot prove" $RESULT; then
            echo $FNAME unproven fail >> $REPORT_FNAME
        fi
        if grep -q "No such variable, constructor, regular function," $RESULT; then
            echo $FNAME syntax fail >> $REPORT_FNAME
        fi
        if grep -q "Parse error." $RESULT; then
            echo $FNAME parser fail >> $REPORT_FNAME
        fi
        if grep -q "Type mismatch." $RESULT; then
            echo $FNAME type fail >> $REPORT_FNAME
        fi
        if grep -q "Wrong number of arguments" $RESULT; then
            echo $FNAME spec fail >> $REPORT_FNAME
        fi
        if grep -q "No such function" $RESULT; then
            echo $FNAME spec fail >> $REPORT_FNAME
        fi
        cat $RESULT
    fi
}

show_result(){
    FNAME=$1
    RESULT=$2
    PROCESSED=$(cat $REPORT_FNAME | wc -l)
    echo "[${PROCESSED}/${TOT_FILES}] $FNAME : $(cat $VALID_RESULT)"
}

validate_file() {
    FNAME=$1
    UNIQUE_PREFIX="${WORK_DIR}/$(echo $FNAME | egrep -o '[[:digit:]]{6}' | head -n1)"
    SRC_FNAME="${UNIQUE_PREFIX}.c"
    VALID_RESULT="${UNIQUE_PREFIX}.validator_result"
    VERIF_RESULT="${UNIQUE_PREFIX}.vf_result"
    cp $FNAME $UNIQUE_PREFIX.src
    CMD1="./validator.byte nat_fspec.cmo $FNAME $SRC_FNAME $UNIQUE_PREFIX $VERIFAST"
    CMD2="$VERIFAST -c -I $SPEC_DIR $SRC_FNAME"
    echo "make all && $CMD1 && $CMD2" > "${UNIQUE_PREFIX}.cmd"
    $CMD1 > $VALID_RESULT && $CMD2 > $VERIF_RESULT
    analyze_result $VERIF_RESULT $FNAME
    show_result $FNAME $(cat $VALID_RESULT)
}

if [ -z "$WORK_DIR" ]; then
    echo "Please set working dir - the second param"
    exit 1;
fi
command -v $VERIFAST >/dev/null 2>&1 ||
    { echo >&2 "I require custom VeriFast in the PATH.  Aborting."; exit 1; }

make all
mkdir -p $WORK_DIR
rm -f $REPORT_FNAME

FILES=$KLEE_OUT_DIR/call-pre*.txt

TOT_FILES=$(ls -l $FILES | wc -l)

export -f validate_file
export -f analyze_result
export -f show_result

export WORK_DIR
export REPORT_FNAME
export VERIFAST
export TOT_FILES
export SPEC_DIR

# executing this file on a container looses the $SHELL value in parallel
export SHELL=/bin/bash
if [ -z "$SINGLE_TEST" ]; then
    parallel validate_file ::: $KLEE_OUT_DIR/call-pre*.txt
else
    PADDED=`printf %06d $SINGLE_TEST`
    validate_file $KLEE_OUT_DIR/call-prefix$PADDED.txt
fi

TOT=$(cat $REPORT_FNAME | wc -l)
SUCC=$(grep -c "success" $REPORT_FNAME)
ASSERT=$(grep -c "assertion fail" $REPORT_FNAME)
NOCHUNKS=$(grep -c "nochunks fail" $REPORT_FNAME)
LEAK=$(grep -c "leak fail" $REPORT_FNAME)
UNPROVEN=$(grep -c "unproven fail" $REPORT_FNAME)
SYNTAX=$(grep -c "syntax fail" $REPORT_FNAME)
PARSER=$(grep -c "parser fail" $REPORT_FNAME)
TYPE=$(grep -c "type fail" $REPORT_FNAME)
SPEC=$(grep -c "spec fail" $REPORT_FNAME)

echo "Test completed."
echo "total: $TOT"
echo "success: $SUCC"
echo "assertion: $ASSERT"
echo "no chunks: $NOCHUNKS"
echo "cannot prove: $UNPROVEN"
echo "leaks: $LEAK"
echo "syntax err: $SYNTAX"
echo "type mismatch $TYPE"
echo "parse errs: $PARSER"
echo "spec errs: $SPEC"
