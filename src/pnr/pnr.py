from util.bimdict import BiMultiDict, BiDict
from smt.solvers import Solver_z3, Solver_monosat
import itertools as it
from smt_switch import solvers

try:
    import pulp
    import pulp.solvers
except:
    pass

PLACE_SOLVER = solvers.Z3Solver()
_ROUTE_SOLVER = Solver_monosat()

''' Class for handling place & route '''
class PNR:
    def __init__(self, fabric, design, place_solver):
        self._fabric = fabric
        self._design = design

        self._place_state = BiMultiDict()
        self._route_state = BiMultiDict()

        self._place_vars = BiDict()
        self._route_vars = BiDict()
        
        self._place_solver = place_solver
        self._route_solver = _ROUTE_SOLVER

        # set options
        self._place_solver.set_option('produce-models', 'true')

    @property
    def place_state(self):
        return self._place_state

    def pin_module(self, module, placement):
        self._place_state[module] = placement
    
    def pin_net(self, net, placement):
        pass

    def place_design(self, funcs, model_reader):
        # Build up a list of all constraints
        for f in funcs:
            constraint = f(self.fabric, self.design, self._place_state, \
                           self._place_vars, self._place_solver)
            self._place_solver.add(constraint)

        # Solve the problem
        if not self._place_solver.check_sat():
            self._place_solver.reset()
            # set options
            self._place_solver.set_option('produce-models', 'true')
            self._place_vars = BiDict()
            return False
        
        model_reader(self.fabric, self.design, self._place_state, self._place_vars, self._place_solver)

        return True


    def route_design(self, funcs, model_reader):
        constraints = []
        for f in funcs:
            c = f(self.fabric, self.design, self._place_state, self._route_state, self._route_vars, self._route_solver)
            self._route_solver.add(self._route_solver.And(c))

        if not self._route_solver.solve():
            return False
        
        
        model_reader(self.fabric, self.design, self._place_state, self._route_state, self._route_vars, self._route_solver)
        return True

    def write_design(self, model_writer):
        model_writer(self._place_state, self._route_state)

    @property
    def fabric(self):
        return self._fabric

    @property
    def design(self):
        return self._design
    
''' MILP solver interface '''
class ValueMILP:
    def __init__(self, value):
        self.value = value

    def as_real(self):
        return float(self.value)

    def as_int(self):
        return int(self.value)
    
    def as_bool(self):
        return bool(self.value)

class ConstraintMILP:
    def __init__(self, clauses=None):
        if clauses is None:
            self.clauses = []
        elif isinstance(clauses, list):
            self.clauses = clauses
        else:
            self.clauses = [clauses]

    def __iter__(self):
        return iter(self.clauses)

    def add(self, clauses):
        if isinstance(clauses, list):
            self.clauses += clauses
        else:
            self.clauses.append(clauses)

class SolverMILP:

    def __init__(self, solverName='gurobi'):

        self.solver = SolverMILP.str2solver(solverName)
        self.problem = pulp.LpProblem('pnr', pulp.LpMinimize)

        self.varCounter = 0

        # define feasibility problem (i.e., minimize 0)
        self.problem += 0

    def EmptyConstraint(self):
        return ConstraintMILP()

    def BinaryVar(self):
        name = 'BIN'+str(self.varCounter)
        self.varCounter += 1
        return pulp.LpVariable(name, cat='Binary')

    @property
    def Real(self):
        return 'Continuous'

    @property
    def Bool(self):
        return 'Binary'

    def ExactlyOne(self, clauses):
        return (pulp.lpSum(clauses) == 1)

    def Equals(self, a, b):
        return (a == b)

    def Plus(self, a, b):
        return (a + b)

    def Minus(self, a, b):
        return (a - b)

    def LUT(self, lut):
        expr = [key*val for key, val in lut.items()]
        return pulp.lpSum(expr)

    def LTE(self, left, right):
        return (left <= right)

    def AtLeastOneNegative(self, clauses):
        constraints = self.EmptyConstraint()

        orVars = []
        for clause in clauses:
            # create new binary variable
            orVar = self.BinaryVar()
            orVars.append(orVar)

            # BigM should be larger than any legal value of clause
            constraints.add(self.LTE(clause, self.BigM*(1-orVar)))

        # at least one must hold
        constraints.add(pulp.lpSum(orVars) >= 1)

        return constraints

    def IsTrue(self, variable):
        return (variable == 1)

    def IsFalse(self, variable):
        return (variable == 0)

    def declare_const(self, name, sort):
        return pulp.LpVariable(name, cat=sort)

    def theory_const(self, sort, value):
        if sort == 'Continuous':
            return value
        elif sort == 'Binary':
            return int(value)

    def get_value(self, variable):
        return ValueMILP(pulp.value(variable))

    def add(self, constraints):
        if isinstance(constraints, list) or \
           isinstance(constraints, ConstraintMILP):
            for constraint in constraints:
                self.add(constraint)
        else:
            self.problem += constraints

    def check_sat(self):
        self.problem.solve(self.solver)
        return True

    def set_option(self, *args):
        pass

    def reset(self):
        pass

    @staticmethod
    def str2solver(solverName, *args, **kwargs):
        return getattr(pulp.solvers, solverName.upper())(*args, **kwargs)
