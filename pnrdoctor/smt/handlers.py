from abc import ABCMeta, abstractmethod

from pnrdoctor.util import NamedIDObject
from . import smt_util as su
from .region import SYMBOLIC


class BaseHandler(NamedIDObject, metaclass=ABCMeta):
    def __init__(self, name, solver):
        super().__init__(name, lambda obj : '{}_{}'.format(obj.name, obj.id))
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

    def __eq__(self, other):
        return self.equal(other)

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
    def __init__(self, name, solver, bits, const_value):
        super().__init__(name, solver)
        self._bits = bits
        if const_value is None:
            self._var = solver.DeclareConst(self.name, solver.BitVec(bits))
        else:
            self._var = self.solver.TheoryConst(self.solver.BitVec(bits), const_value)

    def encode(self, value):
        return type(self)('encoded_{}'.format(value), self.solver, self._bits, value)

    @property
    def value(self):
        return self.solver.GetValue(self._var).as_int()

    @property
    def invariants(self):
        return super().invariants

    @property
    def var(self):
        return self._var

class ScalarHandler(BVHandler):
    def __init__(self, name, solver, upper_bound, const_value=None):
        super().__init__(name, solver, upper_bound.bit_length(), const_value)
        self._upper_bound = upper_bound
        self._is_pow2 = upper_bound & (upper_bound - 1) == 0

    def delta(self, other):
        if isinstance(other, type(self)):
            return self.var - other.var
        return self - self.encode(other)

    def abs_delta(self, other):
        delta = self.delta(other)

        #return self.solver.Ite(delta >= 0, delta, -delta)
        return su.abs_ite(self.solver, delta)

    def distinct(self, other):
        if isinstance(other, type(self)):
            return self._var != other._var
        return self != self.encode(other)

    def equal(self, other):
        if isinstance(other, type(self)):
            return self._var == other._var
        return self.equal(self.encode(other))

    def encode(self, value):
        assert 0 <= int(value) < self._upper_bound, 'Cannot encode given value'
        return type(self)('encoded_{}'.format(value), self.solver, self._upper_bound, value)

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
            c = self.solver.BVUlt(self._var, self._upper_bound)

        return self.solver.And([c, super().invariants])

class CategoryHandler(BVHandler):
    def __init__(self, name, solver, bits, const_value=None):
        super().__init__(name, solver, bits, const_value)

    def distinct(self, other):
        if isinstance(other, type(self)):
            return self._var & other._var == 0
        return self & self.encode(other) == 0

    def equal(self, other):
        if isinstance(other, type(self)):
            return self._var == other._var
        return self.equal(self.encode(other))

    def encode(self, value):
        assert 0 <= int(value) < 2**self._bits, 'Cannot enode given value'
        return super().encode(value)

    @property
    def value(self):
        return self.solver.GetValue(self._var).as_int()

    @property
    def invariants(self):
        return super().invariants

class OneHotHandler(CategoryHandler):
    def encode(self, value):
        assert any(value == (1 << i) for i in range(self._bits)), 'Cannot enode given value'
        return super().encode(value)

    @property
    def invariants(self):
        constraints = []
        for i in range(self._bits):
            constraints.append(self.equal(1 << i))

        return self.solver.And([self.solver.Or(constraints), super().invariants])
