from abc import ABCMeta, abstractmethod
import z3util as zu
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

    @property
    @abstractmethod
    def invariants(self):
        '''
        invariants :: -> z3.Bool
        '''
        pass

    @abstractmethod
    def get_coardinates(self, model):
        '''
        get_coardinates :: z3.ModelRef -> (int, int)

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

    @property
    def invariants(self):
        return z3.And(zu.hamming(self.x) == 1, zu.hamming(self.y) == 1)

    def get_coardinates(self, model):
        return (log2(model.eval(self.x)), log2(model.eval(self.y)))


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


