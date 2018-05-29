echo "Adding paths to solvers"

export PYTHONPATH=$PYTHONPATH:`pwd`/smt_solvers/cvc4
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`pwd`/smt_solvers/cvc4

export PATH=$PATH:`pwd`/smt_solvers/monosat
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`pwd`/smt_solvers/monosat

export PATH=$PATH:`pwd`/smt_solvers/z3/bin/
export PYTHONPATH=$PYTHONPATH:`pwd`/smt_solvers/z3/bin/python/
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`pwd`/smt_solvers/z3/bin

export PYTHONPATH=$PYTHONPATH:`pwd`/smt_solvers/boolector
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`pwd`/smt_solvers/boolector
