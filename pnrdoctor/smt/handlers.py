from abc import ABCMeta, abstractmethod

from pnrdoctor.util import NamedIDObject
from . import smt_util as su
from .region import SYMBOLIC


class BaseHandler(NamedIDObject, metaclass=ABCMeta):
    def __init__(self, name, solver):
        super().__init__(name, lambda obj : '{}_{}'.format(obj.id, obj.name))
        self._solver = solver

    @property
    def solver(self):
        return self._solver

    @abstractmethod
    def distinct(self, other):
        pass

    @abstractmethod
    def equal(self, other):
        pass

    @abstractmethod
    def encode(self, value):
        pass

    @property
    @abstractmethod
    def invariants(self):
        return True

    @property
    @abstractmethod
    def value(self):
        pass


class BVHandler(BaseHandler):
    def __init__(self, name, solver, bits):
        super().__init__(name, solver)
        self._bits = bits
        self._var = solver.DeclareConst(self.name, solver.BitVec(bits))

    def encode(self, value):
        return self.solver.TheoryConst(self.solver.BitVec(self._bits), int(value))

    @property
    def value(self):
        return self.solver.GetValue(self._var).as_int()

    @property
    def invariants(self):
        return super().invariants

class ScalarHandler(BVHandler):
    def __init__(self, name, solver, upper_bound):
        super().__init__(name, solver, upper_bound.bit_length())
        self._upper_bound = upper_bound
        self._is_pow2 = upper_bound & (upper_bound - 1)

    def delta(self, other):
        try:
            return self._var - other._var
        except AttributeError:
            return self._var - self.encode(other)

    def abs_delt(self, other):
        return su.absolute_value(self.delta(other))

    def distinct(self, other):
        try:
            return self._var != other._var
        except AttributeError:
            return self._var != self.encode(other)

    def equal(self, other):
        try:
            return self._var == other._var
        except AttributeError:
            return self._var == self.encode(other)

    def encode(self, value):
        return self.solver.TheoryConst(self.solver.BitVec(self._bits), int(value))

    @property
    def value(self):
        return self.solver.GetValue(self._var).as_int()

    @property
    def invariants(self):
        if self._is_pow2:
            ix = self._bits - 1
            # can use slices with latest version of smt-switch
            # one index means Extract(ix, ix)

            c = self._var[ix] == 0
        else:
            c = bvult(self._var, self._upper_bound)

        return self.solver.And([c, super().invariants])

class CategoryHandler(BVHandler):
    def __init__(self, name, solver, bits):
        super().__init__(name, solver, bits)

    def distinct(self, other):
        try:
            return self._var & other._var == 0
        except AttributeError:
            return self._var & self.encode(other) == 0

    def equal(self, other):
        try:
            return self._var == other._var
        except AttributeError:
            return self._var == self.encode(other)

    def encode(self, value):
        return self.solver.TheoryConst(self.solver.BitVec(self._bits), int(value))

    @property
    def value(self):
        return self.solver.GetValue(self._var).as_int()

    @property
    def invariants(self):
        return super().invariants

class OneHotHandler(CategoryHandler):
    @property
    def invariants(self):
        constraints = []
        for i in range(self._bits):
            constraints.append(self.equal(1 << i))

        return self.solver.And([self.solver.Or(constraints), super().invariants])
