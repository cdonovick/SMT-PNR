#!/bin/bash
PREFIX=$(dirname $0)
TESTS=( "reg.json" "reg2.json" "conv.json" "simp_mem.json" )
FABRICS=( "cgra8x8mr.xml" )
LIBS="stdlib cgralib"
ANNOTATED="${PREFIX}/annoted"
COMMANDS="--annotate $ANNOTATED --print"
LIMIT=300

if [[ "$SOLVER" != "" ]]; then
    COMMANDS="$COMMANDS --solver $SOLVER"
fi

code=0
for d in "${TESTS[@]}"; do
    for f in "${FABRICS[@]}"; do
        cmd="${PREFIX}/../src/run_pnr.py ${PREFIX}/designs/$d ${PREFIX}/fabrics/$f --coreir-libs $LIBS $COMMANDS"
        echo $cmd
        timeout $LIMIT $cmd
        r=$?
        if [ $r -eq 0 ]; then
            echo Success!
            rm $ANNOTATED || echo "Attempted to remove ${ANNOTATED} but failed..."
        elif [ $r -eq 124 ]; then
            echo ???Timeout???
        else
            echo !!!FAILURE!!!
            code=1
        fi
        echo
        echo
    done
done

exit $code
