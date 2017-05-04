from abc import ABCMeta, abstractmethod
import functools as ft
import itertools as it
from math import log2, ceil
import smt.z3util as zu
import z3
from smt_switch import sorts
from smt_switch import functions

And = functions.And()
Or = functions.Or()
concat = functions.concat()


class PositionBase(metaclass=ABCMeta):
    def __init__(self, name, fabric, solver):
        self._name = name
        self._fabric = fabric
        self._solver = solver

    @property
    def name(self):
        return self._name

    @property
    def fabric(self):
        return self._fabric

    @property
    def solver(self):
        return self._solver

    @property
    @abstractmethod
    def flat(self):
        '''
        flat :: -> z3.BitVec | a.flat == b.flat => a.x == b.x and a.y == b.y
nn
        Return (x, y) in some form that such that z3.distinct can be called on it
        '''
        pass

    @property
    @abstractmethod
    def x(self):
        '''
        x :: -> z3.BitVec
        '''
        pass


    @property
    @abstractmethod
    def y(self):
        '''
        y :: -> z3.BitVec
        '''
        pass

    @abstractmethod
    def delta_x(self, other):
        '''
        delta_x :: PositionBase -> (z3.Bool, z3.BitVec)
        '''
        pass

    @abstractmethod
    def delta_y(self, other):
        '''
        delta_y :: PositionBase -> (z3.Bool, z3.BitVec)
        '''
        pass

    @abstractmethod
    def delta_x_fun(self, other):
        '''
        delta_x :: PositionBase -> (int -> z3.Bool)
        builds a function f such that f(c) => delta_x == c
        '''
        pass

    @abstractmethod
    def delta_y_fun(self, other):
        '''
        delta_y :: PositionBase -> (int -> z3.Bool)
        builds a function f such that f(c) => delta_y == c
        '''
        pass


    @property
    @abstractmethod
    def invariants(self):
        '''
        invariants :: -> z3.Bool
        '''
        pass

    @abstractmethod
    def get_coordinates(self, model):
        '''
        get_coordinates :: z3.ModelRef -> (int, int)

        evaluates the model at self and returns 0 indexed x,y coardinates
        '''
        pass


    @abstractmethod
    def encode(self, p):
        '''
        encode :: (int, int) -> z3.BitVec
        '''
        pass
    
    @abstractmethod
    def encode_x(self, x):
        '''
        encode :: int -> z3.BitVec
        '''
        pass

    @abstractmethod
    def encode_y(self, y):
        '''
        encode :: int -> z3.BitVec
        '''
        pass

    def distinct(self, *others):
        '''
        distinct :: z3.BitVec* -> z3.Bool
        '''
        c = []
        for other in others:
            c.append(self.flat != other.flat)
        return And(c)


class Base2H(PositionBase):
    '''
    Base class for 2 hot representations
    '''

    def __init__(self, name, fabric, solver):
        super().__init__(name, fabric, solver)

    @property
    @abstractmethod
    def flat(self):
        '''
        flat :: -> z3.BitVec | a.flat == b.flat => a.x == b.x and a.y == b.y

        Return (x, y) in some form that such that z3.distinct can be called on it
        '''
        pass

    @property
    @abstractmethod
    def x(self):
        '''
        x :: -> z3.BitVec
        '''
        pass


    @property
    @abstractmethod
    def y(self):
        '''
        y :: -> z3.BitVec
        '''
        pass

    def delta_x(self, other):
        delta_x = self.solver.declare_const(self.name+'-'+other.name+'_delta_x', sorts.BitVec(self.fabric.cols))
        constraint = Or(self.x == other.x << delta_x, other.x == self.x << delta_x)
        return constraint, delta_x

    def delta_y(self, other):
        delta_y = self.solver.declare_const(self.name+'-'+other.name+'_delta_y', sorts.BitVec(self.fabric.rows))
        constraint = Or(self.y == other.y << delta_y, other.y == self.y << delta_y)
        return constraint, delta_y

    def delta_x_fun(self, other):
        def delta_fun(constant):
            if constant == 0:
                return self.x == other.x
            else:
                return Or(self.x == other.x << constant, other.x == self.x << constant)
        return delta_fun

    def delta_y_fun(self, other):
        def delta_fun(constant):
            if constant == 0:
                return self.y == other.y
            else:
                return Or(self.y == other.y << constant, other.y == self.y << constant)
        return delta_fun

    @property
    def invariants(self):
        return And(zu.hamming(self.x) == 1, zu.hamming(self.y) == 1)

    def get_coordinates(self):
        return (int(log2(self.solver.get_value(self.x).as_int())), int(log2(self.solver.get_value(self.y).as_int())))

    def encode_x(self, x):
        return self.solver.theory_const(sorts.BitVec(self.fabric.cols), 1 << x)

    def encode_y(self, y):
        return self.solver.theory_const(sorts.BitVec(self.fabric.rows), 1 << y)

    @abstractmethod
    def encode(self, p):
        '''
        encode :: (int, int) -> z3.BitVec
        '''
        pass


class OneHot(Base2H):
    def __init__(self, name, fabric):
        super().__init__(name, fabric)
        self._bv = self.solver.declare_const(self.name, sorts.BitVec(self.fabric.rows * self.fabric.cols))

    @property
    def flat(self):
        '''
        flat :: -> z3.BitVec | a.flat == b.flat => a.x == b.x and a.y == b.y

        Return (x, y) in some form that such that z3.distinct can be called on it
        '''
        return self._bv

    @property
    def x(self):
        '''
        x :: -> z3.BitVec
        '''
        rows = []
        for r in range(self.fabric.rows):
            rows.append(functions.extract((r+1)*self.fabric.cols-1, r*self.fabric.cols)(self._bv))
        x = ft.reduce(lambda a, b: a | b, rows)
        #assert x.size() == self.fabric.cols
        return x

    @property
    def y(self):
        '''
        y :: -> z3.BitVec
        '''
        cols = []
        for c in range(self.fabric.cols):
            col = [] 
            for r in range(self.fabric.rows):
                col.append(functions.extract(c+r*self.fabric.cols, c+r*self.fabric.cols)(self._bv))
            cols.append(ft.reduce(z3.Concat, col))

        y = ft.reduce(lambda a, b: a | b, cols)
        #assert y.size() == self.fabric.rows
        return y


    @property
    def invariants(self):
        '''
        invariants :: -> z3.Bool
        '''
        return zu.hamming(self._bv) == 1

    def encode(self, p):
        '''
        encode :: (int, int) -> z3.BitVec
        '''
        return self.solver.theory_const(sorts.BitVec(self.fabric.cols*self.fabric.rows), 1 << (p[1]*self.fabric.cols + p[0]))

    
    def distinct(self, *other):
        '''
        distinct :: z3.BitVec* -> z3.Bool
        '''
        l = list(other)
        n = len(l) + 1
        return zu.hamming(ft.reduce(lambda acc, b: acc | b.flat, l, self.flat)) == n

class Packed2H(Base2H):
    '''
    2 Hot representation, packed into a single BitVec
    '''
    def __init__(self, name, fabric, solver):
        super().__init__(name, fabric, solver)
        self._flat = self.solver.declare_const(self.name + '_flat', sorts.BitVec(self.fabric.rows + self.fabric.cols))

    @property
    def flat(self):
        return self._flat

    @property
    def x(self):
        ext = functions.extract(self.fabric.rows + self.fabric.cols-1, self.fabric.rows)
        return ext(self.flat)

    @property
    def y(self):
        ext = functions.extract(self.fabric.rows-1, 0)
        return ext(self.flat)

    def encode(self, p):
        return concat(self.encode_x(p[0]), self.encode_y(p[1]))

class Unpacked2H(Base2H):
    '''
    2 Host representation, x and y in seperate BitVec
    '''
    def __init__(self, name, fabric, solver):
        super().__init__(name, fabric, solver)
        self._x = self.solver.declare_const(self.name + '_x', sorts.BitVec(self.fabric.cols))
        self._y = self.solver.declare_const(self.name + '_y', sorts.BitVec(self.fabric.rows))

    @property
    def flat(self):
        return concat(self.x, self.y)

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    def encode(self, p):
        return concat(self.encode_x(p[0]), self.encode_y(p[1]))

class BVXY(PositionBase):
    def __init__(self, name, fabric, solver):
        super().__init__(name, fabric, solver)
        if 2**(self.fabric.cols.bit_length()-1) == self.fabric.cols:
            #adding extra bit to avoid overflow adjacency
            self._x_bits    = self.fabric.cols.bit_length()
            self._is_x_pow2 = True 
        else:
            self._x_bits    = self.fabric.cols.bit_length()
            self._is_x_pow2 = False
        if 2**(self.fabric.rows.bit_length()-1) == self.fabric.rows:
            #adding extra bit to avoid overflow adjacency
            self._y_bits    = self.fabric.rows.bit_length()
            self._is_y_pow2 = True
        else:
            self._y_bits    = self.fabric.rows.bit_length()
            self._is_y_pow2 = False
    
        self._x = z3.BitVec(self.name + '_x', self._x_bits)
        self._y = z3.BitVec(self.name + '_y', self._y_bits)

    def delta_x(self, other):
        return [], zu.absolute_value(self.x - other.x)

    def delta_y(self, other):
        return [], zu.absolute_value(self.y - other.y)

    def delta_x_fun(self, other):
        def delta_fun(constant):
            _, c = self.delta_x(other)
            return c == constant
        return delta_fun

    def delta_y_fun(self, other):
        def delta_fun(constant):
            _, c = self.delta_y(other)
            return c == constant
        return delta_fun

    @property
    def flat(self):
        return concat(self.x, self.y)

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @property
    def invariants(self):
        constraint = []
        if self._is_x_pow2:
            ix = self._x_bits - 1
            ext = functions.extract(ix, ix)
            constraint.append(ext(self.x) == 0)
        else:
            # TODO: switch to solver-agnostic version
            constraint.append(z3.ULT(self.x, self.fabric.cols))
        if self._is_y_pow2:
            iy = self._y_bits - 1
            ext = functions.extract(iy, iy)
            constraint.append(ext(iy, iy, self.y) == 0)
        else:
            # TODO: switch to solver-agnostic version
            constraint.append(z3.ULT(self.y, self.fabric.rows))
        return And(constraint)

    def get_coordinates(self):
        return (self.solver.get_value(self.x).as_int(), self.solver.get_value(self.y).as_int())

    def encode(self, p):
        return self.encode_x(p[0]), self.encode_y(p[1])

    def encode_x(self, x):
        return self.solver.theory_const(sorts.BitVec(self._x_bits), x)

    def encode_y(self, y):
        return self.solver.theory_const(sorts.BitVec(self._y_bits), y)
