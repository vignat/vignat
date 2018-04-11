#!/bin/bash
if [ -z $VERIFAST ]; then VERIFAST="verifast"; fi
KLEE_OUT_DIR=$1
WORK_DIR=$2
SPEC_DIR=$3
FSPEC_PLUGIN=$4
SINGLE_TEST=$5
REPORT_FNAME="${WORK_DIR}/report.txt"
BASE_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"


analyze_result() {
    VL_RESULT=$1
    VF_RESULT=$2
    FNAME=$3
    if [ -e "$VL_RESULT" ]; then
        if grep -q "Valid" $VL_RESULT; then
            echo $FNAME success >> $REPORT_FNAME
        elif grep -q "\\\\/alid" $VL_RESULT; then
            echo $FNAME success >> $REPORT_FNAME
        elif grep -q "Inconsistent" $VL_RESULT; then
            echo $FNAME inconsistent >> $REPORT_FNAME
        else
            cat $VF_RESULT
            if grep -q "Assertion might not hold" $VF_RESULT; then
                echo $FNAME assertion fail >> $REPORT_FNAME
            elif grep -q "No matching heap chunks" $VF_RESULT; then
                echo $FNAME nochunks fail >> $REPORT_FNAME
            elif grep -q "No matching pointsto chunk" $VF_RESULT; then
                echo $FNAME nochunks fail >> $REPORT_FNAME
            elif grep -q "Function leaks heap chunks" $VF_RESULT; then
                echo $FNAME leak fail >> $REPORT_FNAME
            elif grep -q "Cannot prove" $VF_RESULT; then
                echo $FNAME unproven fail >> $REPORT_FNAME
            elif grep -q "Cannot read a ghost variable in a non-pure context" $VF_RESULT; then
                echo $FNAME syntax fail >> $REPORT_FNAME
            elif grep -q "No such variable, constructor, regular function," $VF_RESULT; then
                echo $FNAME syntax fail >> $REPORT_FNAME
            elif grep -q "Incorrect number of arguments" $VF_RESULT; then
                echo $FNAME syntax fail >> $REPORT_FNAME
            elif grep -q "Parse error." $VF_RESULT; then
                echo $FNAME parser fail >> $REPORT_FNAME
            elif grep -q "Type mismatch." $VF_RESULT; then
                echo $FNAME type fail >> $REPORT_FNAME
            elif grep -q "Wrong number of arguments" $VF_RESULT; then
                echo $FNAME spec fail >> $REPORT_FNAME
            elif grep -q "No such function" $VF_RESULT; then
                echo $FNAME spec fail >> $REPORT_FNAME
            elif grep -q "Potential arithmetic" $VF_RESULT; then
                echo $FNAME arith fail >> $REPORT_FNAME
            elif grep -q "Uncaught exception" $VL_RESULT; then
                echo $FNAME validator exception >> $REPORT_FNAME
                cat $VL_RESULT
            else
                echo $FNAME unknown fail >> $REPORT_FNAME
                cat $VL_RESULT
            fi
        fi
    else
        echo $FNAME unknown fail >> $REPORT_FNAME
    fi
}

show_result(){
    FNAME=$1
    RESULT=$2
    PROCESSED=$(cat $REPORT_FNAME | wc -l)
    echo "[${PROCESSED}/${TOT_FILES}] $FNAME : $RESULT"
}

validate_file() {
    FNAME=$1
    UNIQUE_PREFIX="${WORK_DIR}/$(echo $FNAME | egrep -o '[[:digit:]]{6}' | head -n1)"
    VALID_RESULT="${UNIQUE_PREFIX}.validator_result"
    VERIF_RESULT="${UNIQUE_PREFIX}.vf_result"
    cp $FNAME $UNIQUE_PREFIX.src
    CMD1="$BASE_DIR/validator.byte $FSPEC_PLUGIN $FNAME $UNIQUE_PREFIX $VERIFAST $SPEC_DIR"
    echo "(cd $BASE_DIR && make all) && $CMD1" > "${UNIQUE_PREFIX}.cmd"
    $CMD1 &> $VALID_RESULT
    VERIF_RESULT="${UNIQUE_PREFIX}.verify.stdout"
    analyze_result $VALID_RESULT $VERIF_RESULT $FNAME
    show_result $FNAME $(cat $VALID_RESULT)
}

if [ -z "$WORK_DIR" ]; then
    echo "Please set working dir - the second param"
    echo "Invoke the script like this:"
    echo "   $ $0 klee-out-dir wdir spec-dir plugin <test#>"
    echo "Where:"
    echo " klee-out-dir - a directory klee-out-#, created as a result of"
    echo "                the verification pass."
    echo " wdir - working dir: the directory to store all the temporary"
    echo "        files and the final report."
    echo " spec-dir - the root directory of the project. Necessary to find"
    echo "            the include files."
    echo " plugin - the validator plugin file - OCaml dynamic module,"
    echo "          should have a cmo extension. E.g. nat_fspec.cmo"
    echo " test# - optional number of the prefix file to run. If abscent"
    echo "         the validator will run all the prefixes in the given"
    echo "         directory."
    exit 1;
fi
command -v $VERIFAST >/dev/null 2>&1 ||
    { echo >&2 "I require custom VeriFast in the PATH.  Aborting."; exit 1; }

(cd $BASE_DIR && make all)
if [ $? != 0 ]; then exit 1; fi
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
export FSPEC_PLUGIN
export BASE_DIR

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
ARITH=$(grep -c "arith fail" $REPORT_FNAME)
VLEXCEPT=$(grep -c "validator exception" $REPORT_FNAME)
UNKNOWN=$(grep -c "unknown fail" $REPORT_FNAME)
INCONSISTENT=$(grep -c "inconsistent" $REPORT_FNAME)

echo "Test completed."
echo "total:         $TOT"
echo "success:       $SUCC"
echo "inconsistent:  $INCONSISTENT"
echo "assertion:     $ASSERT"
echo "no chunks:     $NOCHUNKS"
echo "cannot prove:  $UNPROVEN"
echo "leaks:         $LEAK"
echo "syntax err:    $SYNTAX"
echo "type mismatch: $TYPE"
echo "parse errs:    $PARSER"
echo "spec errs:     $SPEC"
echo "arithmetic:    $ARITH"
echo "vl exception:  $VLEXCEPT"
echo "unknown fail:  $UNKNOWN"
