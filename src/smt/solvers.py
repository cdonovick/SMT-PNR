from abc import ABCMeta, abstractmethod
import z3
import monosat as ms


class Solver_base(metaclass=ABCMeta):
    @abstractmethod
    def __init__(self):
        self.constraints = []
        self.sat = None

    def add(self, c):
        self.constraints.append(c)


    def reset(self):
        self.constraints = []
        self.sat = None

    @abstractmethod
    def solve(self):
        pass

    @abstractmethod
    def get_model(self):
        pass

class Solver_z3(Solver_base):
    def __init__(self):
        super().__init__()
        self._solver = z3.Solver()
        self.And = z3.And
        self.Or = z3.Or

    def solve(self):
        self._solver.add(self.And(self.constraints))
        self.sat = self._solver.check() == z3.sat
        if self.sat:
            return True
        else:
            return False

    def reset(self):
        super().reset()
        self._solver.reset()

    def get_model(self):
        if self.sat:
            return self._solver.model()
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

class Solver_monosat(Solver_base):
    def __init__(self):
        super().__init__()
        ms.Monosat().init('-decide-theories -route')  # could also use -decide-theories
        self.graphs = []

    def solve(self):
        ms.Assert(self.And(self.constraints))
        self.sat = ms.Solve()
        return self.sat

    def add_graph(self):
        g = ms.Graph()
        self.graphs.append(g)
        return g

    def reset(self):
        super().reset()
        self.graphs = []
        ms.Monosat().init('-decide-theories -route')

    def get_model(self):
        if self.sat:
            return self.graphs
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def And(self, *pargs, **kwargs):
        if pargs == ([],):
            return True

        if not pargs and not kwargs:
            return True
        else:
            return ms.And(*pargs, **kwargs)

    def Or(self, *pargs, **kwargs):
        if not pargs and not kwargs:
            return True
        else:
            return ms.Or(*pargs, **kwargs)

    def Not(self, *args):
        return ms.Not(*args)

    def false(self):
        return ms.false()

    def AssertAtMostOne(self, bools):
        return ms.AssertAtMostOne(bools)
