VERIFAST="$HOME/Downloads/verifast-15.11/bin/verifast"
TMP_FILE="aaa.c"
KLEE_OUT_DIR=$1
SUCC=0
TOT=0
DIFFICULT=0
NOCHUNKS=0
LEAKS=0
NOPROVE=0
SYNTAX=0
PARSER=0
TYPE=0
corebuild -use-menhir validator.byte
for f in $KLEE_OUT_DIR/call-pre*.txt; do
    echo file: $f
    ./validator.byte $f $TMP_FILE && $VERIFAST -c -I ../nat $TMP_FILE > report.txt
    if grep -q "0 errors found" report.txt; then
        SUCC=$((SUCC+1))
    else
        if grep -q "Assertion might not hold" report.txt; then
            DIFFICULT=$((DIFFICULT+1))
        fi
        if grep -q "No matching heap chunks" report.txt; then
            NOCHUNKS=$((NOCHUNKS+1))
        fi
        if grep -q "Function leaks heap chunks" report.txt; then
            LEAKS=$((LEAKS+1))
        fi
        if grep -q "Cannot prove" report.txt; then
            NOPROVE=$((NOPROVE+1))
        fi
        if grep -q "No such variable, constructor, regular function," report.txt; then
            SYNTAX=$((SYNTAX+1))
        fi
        if grep -q "Parse error." report.txt; then
            PARSER=$((PARSER+1))
        fi
        if grep -q "Type mismatch." report.txt; then
            TYPE=$((TYPE+1))
        fi
        cat report.txt
        echo "To reproduce:\n"
        echo "corebuild -use-menhir validator.byte && ./validator.byte $f $TMP_FILE && $VERIFAST -c -I ../nat $TMP_FILE"
        echo ""
    fi
    TOT=$((TOT+1))
done

echo "total: $TOT success: $SUCC difficult: $DIFFICULT no chunks: $NOCHUNKS cannot prove: $NOPROVE leaks: $LEAKS syntax err: $SYNTAX type mismatch $TYPE parse errs: $PARSER"
