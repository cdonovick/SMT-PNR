from pnrdoctor.smt.region import SYMBOLIC

from pnrdoctor.smt.handlers import BaseHandler


class ILPScalarHandler(BaseHandler):
    def __init__(self, name, solver, upper_bound, const_value=None):
        super().__init__(name, solver)
        self._solver = solver
        self._upper_bound = upper_bound
        self._var = solver.addIntVar(name)

    def distinct(self, other):
        raise NotImplementedError("Use distinct constraint")

    def equal(self, other):
        try:
            return self._var == other._var
        except AttributeError:
            return self._var == self.encode(other)

    def encode(self, value):
        '''
        No encoding needed for ILP solvers
        '''
        return value

    @property
    def invariants(self):
        c = [self._var >= 0,
             self._var <= self._upper_bound - 1]
        return c    

    @property
    def value(self):
        return self._solver.getVal(self._var)

    @property
    def var(self):
        return self._var
