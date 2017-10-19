#!/bin/bash
PREFIX=$(dirname $0)
TESTS=$PREFIX/designs/*
FABRICS=$PREFIX/cgra_8_8_info.xml
LIBS="cgralib"
ANNOTATED="${PREFIX}/annotated"
COMMANDS="--time --noroute"
LIMIT=60

if [[ "$SOLVER" != "" ]]; then
    COMMANDS="$COMMANDS --solver $SOLVER"
fi

code=0
for d in $TESTS; do
    for f in $FABRICS; do
        cmd="${PREFIX}/../run_pnr.py $d $f --coreir-libs $LIBS $COMMANDS"
        echo $cmd
        timeout $LIMIT $cmd
        r=$?
        if [ $r -eq 0 ]; then
            echo Success!
            #rm $ANNOTATED
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
