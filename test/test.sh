#!/bin/bash
PREFIX=$(dirname $0)
TESTS=( "reg.json" "reg2.json" "conv.json" "simp_mem.json" )
FABRICS=( "cgra8x8mr.xml" )
LIBS="stdlib cgralib"
ANNOTATED="${PREFIX}/annoted"
COMMANDS="--annotate $ANNOTATED"

if [[ "$SOLVER" != "" ]]; then
    COMMANDS="$COMMANDS --solver $SOLVER"
fi

for d in "${TESTS[@]}"; do
    for f in "${FABRICS[@]}"; do
        echo "${PREFIX}/../src/run_pnr.py ${PREFIX}/designs/$d ${PREFIX}/fabrics/$f --coreir-libs $LIBS $COMMANDS"
        ${PREFIX}/../src/run_pnr.py ${PREFIX}/designs/$d ${PREFIX}/fabrics/$f --coreir-libs $LIBS $COMMANDS
        if [ $? -eq 0 ]; then
            echo Success!
            cat $ANNOTATED
        else
            echo !!!FAILURE!!!
        fi
        echo
        echo
    done
done

rm -f $ANNOTATED
