#!/bin/bash

solver_dirs=(cvc4 z3 monosat)

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

echo "Adding paths to solvers"

export PYTHONPATH=$PYTHONPATH:`pwd`/smt_solvers/cvc4
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`pwd`/smt_solvers/cvc4

export PATH=$PATH:`pwd`/smt_solvers/monosat
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`pwd`/smt_solvers/monosat
pip install -e smt_solvers/monosat/python

export PATH=$PATH:`pwd`/smt_solvers/z3/bin/
export PYTHONPATH=$PYTHONPATH:`pwd`/smt_solvers/z3/bin/python/
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`pwd`/smt_solvers/z3/bin
