echo "Adding paths to solvers"

: "${SMT_SOLVER_PATH:=$PWD}"

echo Using SMT_SOLVER_PATH=$SMT_SOLVER_PATH

export PYTHONPATH=$PYTHONPATH:$SMT_SOLVER_PATH/smt_solvers/cvc4
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$SMT_SOLVER_PATH/smt_solvers/cvc4

export PATH=$PATH:$SMT_SOLVER_PATH/smt_solvers/monosat
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$SMT_SOLVER_PATH/smt_solvers/monosat

export PATH=$PATH:$SMT_SOLVER_PATH/smt_solvers/z3/bin/
export PYTHONPATH=$PYTHONPATH:$SMT_SOLVER_PATH/smt_solvers/z3/bin/python/
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$SMT_SOLVER_PATH/smt_solvers/z3/bin

export PYTHONPATH=$PYTHONPATH:$SMT_SOLVER_PATH/smt_solvers/boolector
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$SMT_SOLVER_PATH/smt_solvers/boolector
