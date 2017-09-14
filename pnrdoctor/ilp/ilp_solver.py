from abc import ABCMeta, abstractmethod
from collections import Sequence
try:
    from pyscipopt import Model, quicksum
except ImportError:
    pass
try:
    import cvxpy
except ImportError:
    pass


class ILPSolverBase(metaclass=ABCMeta):
    def __init__(self):
        self._boolid = 0

    @abstractmethod
    def addBinVar(self):
        pass

    @abstractmethod
    def addIntVar(self):
        pass

    @abstractmethod
    def Reset(self):
        pass

    @abstractmethod
    def Assert(self, *constraints):
        pass

    @abstractmethod
    def CheckSat(self):
        pass

    @abstractmethod
    def quicksum(self, l):
        pass

    def And(self, l):
        '''
           Returns flattened list -- how our ILP encoding handles And
        '''
        return [item for sublist in l for item in sublist]


class SCIPSolver(ILPSolverBase):
    def __init__(self):
        super().__init__()
        self.model = Model("ILP-PNR")

    def addBinVar(self):
        b = self.model.addVar("b{}".format(self._boolid), vtype="B")
        self._boolid += 1
        return b

    def addIntVar(self, name):
        return self.model.addVar(name, vtype="INTEGER")

    def Reset(self):
        self.model = Model("ILP-PNR")
        self._boolid = 0

    def Assert(self, *constraints):
        assert len(constraints) > 0, "Expecting at least one constraint"
        if isinstance(constraints[0], Sequence):
            constraints = constraints[0]

        for c in constraints:
            self.model.addCons(c)

    def getVal(self, var):
        return self.model.getVal(var)

    def assoc_bool(self, *constraints):
        assert len(constraints) > 0

        if isinstance(constraints[0], Sequence):
            constraints = constraints[0]

        b = self.model.addVar("b{}".format(self._boolid), vtype="B")
        self._boolid += 1

        for c in constraints:
            self.model.addConsIndicator(c, binvar=b)

        return b

    def CheckSat(self):
        self.model.optimize()
        if self.model.getStatus() != "infeasible":
            return True
        else:
            return False

    def quicksum(self, l):
        assert isinstance(l, list)
        return quicksum(l)


class CVXSolver(ILPSolverBase):
    def __init__(self, solver):
        super().__init__()
        self._solver = solver
        self._solver_dict = {"Gurobi": cvxpy.GUROBI}
        self._constraints = []

    def addBinVar(self):
        self._boolid += 1
        return cvxpy.Bool()

    def addIntVar(self, name):
        # name is unused for cvxpy
        return cvxpy.Int()

    def Reset(self):
        self._constraints = []

    def Assert(self, *constraints):
        assert len(constraints) > 0, "Expecting at least one constraint"
        if isinstance(constraints[0], Sequence):
            constraints = constraints[0]

        self._constraints += list(constraints)

    def getVal(self, var):
        return var.value

    def CheckSat(self):
        obj = cvxpy.Minimize(0)
        self._prob = cvxpy.Problem(obj, self._constraints)
        self._prob.solve(solver=self._solver_dict[self._solver], verbose=True)
        if "infeasible" not in self._prob.status.lower():
            return True
        else:
            return False

    def quicksum(self, l):
        return sum(l)


ilp_solvers = {"SCIP": lambda: SCIPSolver(),
               "Gurobi": lambda: CVXSolver("Gurobi")}
