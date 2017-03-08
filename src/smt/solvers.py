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

    @classmethod
    def And(cls, *pargs, **kwargs):
        return cls.And(*pargs, **kwargs)

    @classmethod
    def Or(cls, *pargs, **kwargs):
        return cls.Or(*pargs, **kwargs)

    @abstractmethod
    def solve(self):
        pass

    @abstractmethod
    def get_model(self):
        pass

class Solver_z3(Solver_base):
    And = z3.And
    Or = z3.Or
    def __init__(self):
        super().__init__()
        self._solver = z3.Solver()

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

class Solver_monosat:
    And = ms.And
    Or = ms.Or

    def __init__(self):
        super().__init__()
        self.g = ms.Graph()

    def solve(self):
        self.sat = ms.Solve(self.And(self.constraints))
        return self.sat

    def reset(self):
        super().__init__()
        self.g = ms.Graph()

    def get_model(self):
        if self.sat:
            return self.g
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')
