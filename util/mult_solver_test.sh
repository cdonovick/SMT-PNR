#!/bin/bash

solvers=(Z3 CVC4 Boolector)

# Assuming at top level directory
cd ./src

for solver in "${solvers[@]}"
do
    echo "Testing with placement solver = ${solver}"
    ./test.py ../new_coremapped.json ../cgra4x4.xml \
    --annotate ../bitstream \
    --solver "${solver}" \
    --print \
    --coreir-libs stdlib cgralib
done
