#!/bin/bash

solver_dirs=(solver_binaries)

for solver_dir in "${solver_dirs[@]}"
do
    if [ -d "`pwd`$solver_dir" ]; then
        echo "Found solvers"
    else
        echo "Retrieving solvers"
        wget http://web.stanford.edu/~makaim/files/solver_binaries.tar.gz
        tar -xzvf ./solver_binaries.tar.gz
    fi
    export PYTHONPATH=$PYTHONPATH:$PWD/solver_binaries
    export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$PWD/solver_binaries
done
