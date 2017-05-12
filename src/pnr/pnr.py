from util.bimdict import BiMultiDict, BiDict
from smt.solvers import Solver_z3, Solver_monosat
import itertools as it
from smt_switch import solvers

try:
    import pulp
    import pulp.solvers
except:
    pass

''' Class for handling place & route '''
class PNR:
    def __init__(self, fabric, design, placement_type, 
                 place_solver=None, route_solver=None):
        self._fabric = fabric
        self._design = design
        self._placement_type = placement_type
        self._place_solver = place_solver
        self._route_solver = route_solver

    def init_placement(self):
        # placement solver variables
        self._place_vars = BiDict()

        # placement solver results
        self._place_state = BiMultiDict()

        # default to Z3 solver
        if self._place_solver is None:
            self._place_solver = solvers.Z3Solver()

        # set solver options
        self._place_solver.set_option('produce-models', 'true')
        
        # instantiate design variables
        for module in self.design.modules:
            p = self._placement_type(name=module.name, 
                                     fabric=self.fabric, 
                                     solver=self._place_solver)
            self._place_vars[module] = p

    def place_design(self, funcs, model_reader):
        self.init_placement()

        # Build up a list of all constraints
        for f in funcs:
            f(self.fabric, self.design, self._place_state,
              self._place_vars, self._place_solver)

        # Solve the problem
        if not self._place_solver.check_sat():
            self._place_solver.reset()
            # set options
            self._place_solver.set_option('produce-models', 'true')
            self._place_vars = BiDict()
            return False
        
        # Read out the placement results
        model_reader(self.fabric, self.design, self._place_state, 
                     self._place_vars, self._place_solver)

        return True

    def init_routing(self):
        self._route_state = BiMultiDict()
        self._route_vars = BiDict()

        # default to monosat for routing
        if self._route_solver is None:
            self._route_solver = Solver_monosat()

    def route_design(self, funcs, model_reader):
        self.init_routing()

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

    @property
    def place_state(self):
        return self._place_state

    def pin_module(self, module, placement):
        self._place_state[module] = placement
    
    def pin_net(self, net, placement):
        pass
    
''' MILP solver interface '''
class SolverMILP:

    def __init__(self, solverName='gurobi'):
        # store solver name
        self.solverName = solverName

        self.reset()

    def uniqueVar(self, sort):
        return self.declare_const(name=self.uniqueVarName(sort), sort=sort)

    def uniqueVarName(self, sort):
        # create the category type if it doesn't exist
        if sort not in self.varDict:
            self.varDict[sort] = -1

        # increment the name counter
        self.varDict[sort] += 1

        # create a name that should be unique
        # (uniqueness will be checked upon creation
        # of the variable)
        name = sort + str(self.varDict[sort])

        return name

    @property
    def Real(self):
        return 'Continuous'

    @property
    def Bool(self):
        return 'Binary'

    def exactly_one(self, binVars):
        self.add(pulp.lpSum(binVars) == 1)

    def at_least_one_nonpos(self, exprs):
        orVars = []
        for expr in exprs:
            # create new binary variable
            orVar = self.uniqueVar(self.Bool)
            orVars.append(orVar)

            # BigM should be larger than any legal value of clause
            self.add(expr <= self.BigM*(1-orVar))

        self.add(pulp.lpSum(orVars) >= 1)

    def is_true(self, variable):
        self.add(variable == 1)

    def is_false(self, variable):
        self.add(variable == 0)

    def lut_expr(self, lut):
        exprs = [key*val for key, val in lut.items()]
        return pulp.lpSum(exprs)

    def declare_const(self, name, sort):
        # Check that there is no naming collision
        if name in self.nameSet:
            raise Exception('Variable with this name already exists: ' + name)
        
        # Add name to the name set
        self.nameSet.add(name)

        # Return the variable
        return pulp.LpVariable(name, cat=sort)

    def theory_const(self, sort, value):
        if sort == 'Continuous':
            return value
        elif sort == 'Binary':
            return int(value)

    def get_value(self, variable):
        value = pulp.value(variable)
        if variable.isBinary():
            return bool(value)
        elif variable.isInteger():
            return int(value)
        else:
            return float(value)

    def add(self, constraint):
        self.problem += constraint

    def check_sat(self):
        solver = SolverMILP.str2solver(self.solverName)
        self.problem.solve(solver)

        # TODO: check solver status
        return True

    def set_option(self, *args):
        pass

    def reset(self):
        # variables used to generate unique names
        self.varDict = {}
        self.nameSet = set()

        # define feasibility problem (i.e., minimize 0)
        self.problem = pulp.LpProblem('pnr', pulp.LpMinimize)
        self.problem += 0

    @staticmethod
    def str2solver(solverName, *args, **kwargs):
        return getattr(pulp.solvers, solverName.upper())(*args, **kwargs)
