from abc import ABCMeta, abstractmethod
from math import log2, ceil
import smt.z3util as zu
import z3

class PositionBase(metaclass=ABCMeta):
    def __init__(self, name, fabric):
        self._name = name
        self._fabric = fabric

    @property
    def name(self):
        return self._name

    @property
    def fabric(self):
        return self._fabric

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



class Base2H(PositionBase):
    '''
    Base class for 2 hot representations
    '''

    def __init__(self, name, fabric):
        super().__init__(name, fabric)

    def delta_x(self, other):
        delta_x = z3.BitVec(self.name+'-'+other.name+'_delta_x', self.fabric.cols)
        constraint = z3.Or(self.x == other.x << delta_x, other.x == self.x << delta_x)
        return constraint, delta_x

    def delta_y(self, other):
        delta_y = z3.BitVec(self.name+'-'+other.name+'_delta_y', self.fabric.rows)
        constraint = z3.Or(self.y == other.y << delta_y, other.y == self.y << delta_y)
        return constraint, delta_y

    def delta_x_fun(self, other):
        def delta_fun(constant):
            if constant == 0:
                return self.x == other.x
            else:
                return z3.Or(self.x == other.x << constant, other.x == self.x << constant)
        return delta_fun

    def delta_y_fun(self, other):
        def delta_fun(constant):
            if constant == 0:
                return self.y == other.y
            else:
                return z3.Or(self.y == other.y << constant, other.y == self.y << constant)
        return delta_fun

    @property
    def invariants(self):
        return z3.And(zu.hamming(self.x) == 1, zu.hamming(self.y) == 1)

    def get_coordinates(self, model):
        return (int(log2(model.eval(self.x).as_long())), int(log2(model.eval(self.y).as_long())))


class Packed2H(Base2H):
    '''
    2 Hot representation, packed into a single BitVec
    '''
    def __init__(self, name, fabric):
        super().__init__(name, fabric)
        self._flat = z3.BitVec(self.name + '_flat', self.fabric.rows + self.fabric.cols)

    @property
    def flat(self):
        return self._flat

    @property
    def x(self):
        return z3.Extract(self.fabric.rows + self.fabric.cols-1, self.fabric.rows, self.flat)

    @property
    def y(self):
        return z3.Extract(self.fabric.rows-1, 0, self.flat)

class Unpacked2H(Base2H):
    '''
    2 Host representation, x and y in seperate BitVec
    '''
    def __init__(self, name, fabric):
        super().__init__(name, fabric)
        self._x = z3.BitVec(self.name + '_x', self.fabric.cols)
        self._y = z3.BitVec(self.name + '_y', self.fabric.rows)

    @property
    def flat(self):
        return z3.Concat(self.x, self.y)

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y


class BVXY(PositionBase):
    def __init__(self, name, fabric):
        super().__init__(name, fabric)
        if 2**(self.fabric.cols.bit_length()-1) == self.fabric.cols:
            #adding extra bit to avoid overflow adjacency
            self._x = z3.BitVec(self.name + '_x', 1+self.fabric.cols.bit_length())
            self._is_x_pow2 = True
        else:
            self._x = z3.BitVec(self.name + '_x', self.fabric.cols.bit_length())
            self._is_x_pow2 = False
        if 2**(self.fabric.rows.bit_length()-1) == self.fabric.rows:
            #adding extra bit to avoid overflow adjacency
            self._y = z3.BitVec(self.name + '_y', 1+self.fabric.rows.bit_length())
            self._is_y_pow2 = True
        else:
            self._y = z3.BitVec(self.name + '_y', self.fabric.rows.bit_length())
            self._is_y_pow2 = False

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
        return z3.Concat(self.x, self.y)

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
            ix = self.fabric.cols.bit_length()
            constraint.append(z3.Extract(ix, ix, self.x) == 0)
        else:
            constraint.append(z3.ULT(self.x, self.fabric.cols))
        if self._is_y_pow2:
            iy = self.fabric.rows.bit_length()
            constraint.append(z3.Extract(iy, iy, self.y) == 0)
        else:
            constraint.append(z3.ULT(self.y, self.fabric.rows))
        return z3.And(constraint)

    def get_coordinates(self, model):
        return (model.eval(self.x).as_long(), model.eval(self.y).as_long())

