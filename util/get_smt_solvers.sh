#!/bin/bash

solver_dirs=(cvc4 z3 monosat boolector)

echo "Scanning for solvers"

all_solvers=true

for solver_dir in "${solver_dirs[@]}"
do
    if [ ! -d "`pwd`/smt_solvers/$solver_dir" ]; then
        echo "Missing at least $solver_dir and possibly more"
        echo "Retrieving solvers"
        rm -rf ./smt_solvers
        wget http://web.stanford.edu/~makaim/files/smt_solvers.tar.gz
        tar -xzvf ./smt_solvers.tar.gz
        all_solvers=false
        break
    fi
done

if $all_solvers; then
    echo "Found all solvers"
fi
