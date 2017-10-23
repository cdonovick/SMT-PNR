from abc import ABCMeta, abstractmethod
import z3
import monosat as ms
import itertools
import random


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
        ms.Monosat().init('-decide-theories -route')
        # dictionary to graphs with arbitrary index
        # often layer --> graph
        self.graphs = dict()
        self.at_most_one_builtin_size = 10

    def solve(self, *args):
#        ms.Assert(self.And(self.constraints))
        self.sat = ms.Solve(*args)
        return self.sat

    def add(self, constraints):
        ms.Assert(constraints)

    def add_graph(self, layer):
        g = ms.Graph()
        self.graphs[layer] = g
        return g

    def reset(self):
        super().reset()
        self.graphs = dict()
        ms.Monosat().init('-decide-theories -route')

    def set_option(self, opt, val):
        if opt == 'random-seed':
            random.seed(val)
        else:
            raise ValueError('{} is not yet a supported option'.format(opt))

    def get_model(self):
        if self.sat:
            return self.graphs
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def And(self, *pargs, **kwargs):
        if pargs == ([],):
            return ms.true()

        if not pargs and not kwargs:
            return ms.true()
        else:
            return ms.And(*pargs, **kwargs)

    def Or(self, *pargs, **kwargs):
        if not pargs and not kwargs:
            return True
        else:
            return ms.Or(*pargs, **kwargs)

    def Eq(self, *pargs, **kwargs):
        return ms.Eq(*pargs, **kwargs)

    def Not(self, *args):
        return ms.Not(*args)

    def false(self):
        return ms.false()

    def AtMostOne(self, vars):
        '''
           Copied from https://github.com/sambayless/monosat/blob/master/examples/routing/router_multi.py
           courtesy of Sam Bayless
        '''
        if len(vars) <= self.at_most_one_builtin_size:
            for a, b in itertools.combinations(vars, 2):
                ms.AssertOr(~a, ~b)  # in every distinct pair of edges, at least one must be false
        else:
            ms.AssertAtMostOne(vars) # use more expensive, but more scalable, built-in AMO theory

    def AssertAtMostOne(self, bools):
        return ms.AssertAtMostOne(bools)
