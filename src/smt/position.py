from abc import ABCMeta, abstractmethod
from math import log2
import smt.z3util as zu
from util import NamedIDObject


class PositionBase(NamedIDObject, metaclass=ABCMeta):
    def __init__(self, name, fabric, solver):
        super().__init__(name, lambda obj : '{}_{}'.format(obj.id, obj.name))
        self._fabric = fabric
        self._solver = solver

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

    @property
    @abstractmethod
    def c(self):
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

class Base2H(PositionBase):
    '''
    Base class for 2 hot representations
    '''

    def __init__(self, name, fabric, solver):
        super().__init__(name, fabric, solver)

    def delta_x(self, other):
        delta_x = self.solver.DeclareConst(self.name+'-'+other.name+'_delta_x', self.solver.BitVec(self.fabric.cols))
        constraint = self.solver.Or(self.x == other.x << delta_x, other.x == self.x << delta_x)
        return constraint, delta_x

    def delta_y(self, other):
        delta_y = self.solver.DeclareConst(self.name+'-'+other.name+'_delta_y', self.solver.BitVec(self.fabric.rows))
        constraint = self.solver.Or(self.y == other.y << delta_y, other.y == self.y << delta_y)
        return constraint, delta_y

    def delta_x_fun(self, other):
        def delta_fun(constant):
            if constant == 0:
                return self.x == other.x
            else:
                return self.solver.Or(self.x == other.x << constant, other.x == self.x << constant)
        return delta_fun

    def delta_y_fun(self, other):
        def delta_fun(constant):
            if constant == 0:
                return self.y == other.y
            else:
                return self.solver.Or(self.y == other.y << constant, other.y == self.y << constant)
        return delta_fun

    @property
    def invariants(self):
        return self.solver.And(zu.hamming(self.x) == 1, zu.hamming(self.y) == 1)

    def get_coordinates(self):
        return (int(log2(self.solver.GetValue(self.x).as_int())), int(log2(self.solver.GetValue(self.y).as_int())))

    def encode_x(self, x):
        return self.solver.TheoryConst(self.solver.BitVec(self.fabric.cols), 2**x)

    def encode_y(self, y):
        return self.solver.TheoryConst(self.solver.BitVec(self.fabric.rows), 2**y)

class Packed2H(Base2H):
    '''
    2 Hot representation, packed into a single BitVec
    '''
    def __init__(self, name, fabric, solver):
        super().__init__(name, fabric, solver)
        self._flat = self.solver.DeclareConst(self.name + '_flat', self.solver.BitVec(self.fabric.rows + self.fabric.cols))

    @property
    def flat(self):
        return self._flat

    @property
    def x(self):
        return self.solver.Extract(self.fabric.rows + self.fabric.cols-1, self.fabric.rows, self.flat)

    @property
    def y(self):
        return self.solver.Extract(self.fabric.rows-1, 0, self.flat)

    def encode(self, p):
        return self.solver.Concat(self.encode_x(p[0]), self.encode_y(p[1]))

class Unpacked2H(Base2H):
    '''
    2 Host representation, x and y in seperate BitVec
    '''
    def __init__(self, name, fabric, solver):
        super().__init__(name, fabric, solver)
        self._x = self.solver.DeclareConst(self.name + '_x', self.solver.BitVec(self.fabric.cols))
        self._y = self.solver.DeclareConst(self.name + '_y', self.solver.BitVec(self.fabric.rows))

    @property
    def flat(self):
        return self.solver.Concat(self.x, self.y)

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    def encode(self, p):
        return self.solver.Concat(self.encode_x(p[0]), self.encode_y(p[1]))


class BVXY(PositionBase):
    def __init__(self, name, fabric, solver):
        super().__init__(name, fabric, solver)

        self._is_x_pow2 = self.fabric.cols & (self.fabric.cols - 1) == 0
        self._x_bits = self.fabric.cols.bit_length()

        self._is_y_pow2 = self.fabric.rows & (self.fabric.rows - 1) == 0
        self._y_bits = self.fabric.rows.bit_length()

        self._is_c_pow2 = self.fabric.num_tracks & (self.fabric.num_tracks -1) == 0
        self._c_bits = self.fabric.num_tracks.bit_length()

        self._x = solver.DeclareConst(self.name + '_x', self.solver.BitVec(self._x_bits))
        self._y = solver.DeclareConst(self.name + '_y', self.solver.BitVec(self._y_bits))
        self._c = solver.DeclareConst(self.name + '_color', self.solver.BitVec(self._c_bits))

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
        return self.solver.Concat(self.x, self.y)

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @property
    def c(self):
        return self._c

    @property
    def invariants(self):
        bvult = self.solver.BVUlt
        constraint = []
        if self._is_x_pow2:
            ix = self._x_bits - 1
            # can use slices with latest version of smt-switch
            # one index means Extract(ix, ix)
            constraint.append(self.x[ix] == 0)
        else:
            constraint.append(bvult(self.x, self.fabric.cols))
        if self._is_y_pow2:
            iy = self._y_bits - 1
            constraint.append(self.y[iy] == 0)
        else:
            constraint.append(bvult(self.y, self.fabric.rows))

        if self._is_c_pow2:
            ic = self._c_bits - 1
            constraint.append(self.c[ic]  == 0)
        else:
            constraint.append(bvult(self.c, self.fabric.num_tracks))

        return self.solver.And(constraint)

    def get_coordinates(self):
        return (self.solver.GetValue(self.x).as_int(), self.solver.GetValue(self.y).as_int())

    def get_color(self):
        return (self.solver.GetValue(self.c).as_int())

    def encode(self, p):
        return self.solver.Concat(self.encode_x(p[0]), self.encode_y(p[1]))

    def encode_x(self, x):
        return self.solver.TheoryConst(self.solver.BitVec(self._x_bits), x)

    def encode_y(self, y):
        return self.solver.TheoryConst(self.solver.BitVec(self._y_bits), y)

    def encode_c(self, c):
        return self.solver.TheoryConst(self.solver.BitVec(self._c_bits), c)

