from abc import ABCMeta, abstractmethod
from math import log2, radians, degrees
import smt.z3util as zu
import z3
from smt_switch import sorts
from smt_switch import functions

And = functions.And()
Or = functions.Or()
concat = functions.concat()

class PlacementBase:
    def __init__(self, name, fabric, solver, position, rotation, layer):
        self.name = name
        self.fabric = fabric
        self.solver = solver
        self._position = position
        self._rotation = rotation
        self._layer = layer

    @property
    def position(self):
        return self._position

    @property
    def rotation(self):
        return self._rotation

    @property
    def layer(self):
        return self._layer

    @property
    def hasPosition(self):
        return self.position is not None
    
    @property
    def hasRotation(self):
        return self.rotation is not None

    @property
    def hasLayer(self):
        return self.layer is not None

    @property
    def invariants(self):
        constraints = self.solver.EmptyConstraint()

        if self.hasPosition:
            constraints.add(self.position.invariants)
        if self.hasRotation:
            constraints.add(self.rotation.invariants)
        if self.hasLayer:
            constraints.add(self.layer.invariants)

        return constraints

    def equals(self, position=None, rotation=None, layer=None):
        constraints = self.solver.EmptyConstraint()

        if position is not None:
            constraints.add(self.position.equals(position))
        if rotation is not None:
            constraints.add(self.rotation.equals(rotation))
        if layer is not None:
            constraints.add(self.layer.equals(layer))

        return constraints
    
    def decode(self):
        if self.hasPosition:
            position = self.position.decode()
        else:
            position = None

        if self.hasRotation:
            rotation = self.rotation.decode()
        else:
            rotation = None
        
        if self.hasLayer:
            layer = self.layer.decode()
        else:
            layer = None

        return PlacementConst(position, rotation, layer)

class PlacementConst(PlacementBase):
    def __init__(self, position=None, rotation=None, layer=None):
        super().__init__(name=None, fabric=None, solver=None,
                         position=position, rotation=rotation, layer=layer)

class PcbPlacement(PlacementBase):
    def __init__(self, name, fabric, solver):
        position = PositionReal(name, fabric, solver)
        rotation = Rotation4(name, fabric, solver)
        layer = Layer2(name, fabric, solver)
        super().__init__(name=name, fabric=fabric, solver=solver,
                         position=position, rotation=rotation,
                         layer=layer)

    def distinct(self, other):

        def constraint(shape1, shape2):
            opts = [self.solver.Minus( self.xmax(shape1), other.xmin(shape2)),
                    self.solver.Minus(other.xmax(shape2),  self.xmin(shape1)),
                    self.solver.Minus( self.ymax(shape1), other.ymin(shape2)),
                    self.solver.Minus(other.ymax(shape2),  self.ymin(shape1))]
            return self.solver.AtLeastOneNegative(opts)

        return constraint

    def inShape(self, outside):
        
        def toReal(val):
            return self.solver.theory_const(self.solver.Real, val)

        def constraint(inside):
            obj = self.solver.EmptyConstraint()

            obj.add(self.solver.LTE(toReal(outside.xmin), self.xmin(inside)))
            obj.add(self.solver.LTE(self.xmax(inside), toReal(outside.xmax)))

            obj.add(self.solver.LTE(toReal(outside.ymin), self.ymin(inside)))
            obj.add(self.solver.LTE(self.ymax(inside), toReal(outside.ymax)))

            return obj
        
        return constraint

    def xmin(self, shape):
        return self.solver.Plus(self.position.x, self.shapeLUT(shape, 'xmin'))

    def xmax(self, shape):
        return self.solver.Plus(self.position.x, self.shapeLUT(shape, 'xmax'))

    def ymin(self, shape):
        return self.solver.Plus(self.position.y, self.shapeLUT(shape, 'ymin'))

    def ymax(self, shape):
        return self.solver.Plus(self.position.y, self.shapeLUT(shape, 'ymax'))

    def shapeLUT(self, shape, prop):

        def toReal(val):
            return self.solver.theory_const(self.solver.Real, val)

        lut = {}
        for deg in [0, 90, 180, 270]:
            # compute position of shape property after rotation
            rad = radians(deg)
            rotPos = getattr(shape.rotate(rad), prop)
            rotPos = toReal(rotPos)
        
            # store the shape property in the lookup table
            key = self.rotation.rot(deg)
            lut[key] = rotPos
            
        return self.solver.LUT(lut)

class PositionReal:
    def __init__(self, name, fabric, solver):
        self._name = name
        self._fabric = fabric
        self._solver = solver
        self._x = solver.declare_const(self.name + '_x', solver.Real)
        self._y = solver.declare_const(self.name + '_y', solver.Real)

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
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @property
    def invariants(self):
        return self.solver.EmptyConstraint()

    def decode(self):
        return (self.solver.get_value(self.x).as_real(),
                self.solver.get_value(self.y).as_real())

    def equals(self, p):
        def toReal(val):
            return self.solver.theory_const(self.solver.Real, val)
        
        constraints = self.solver.EmptyConstraint()
        
        constraints.add(self.solver.Equals(self.x, toReal(p[0])))
        constraints.add(self.solver.Equals(self.y, toReal(p[1])))

        return constraints

class Rotation4:
    def __init__(self, name, fabric, solver):
        self._name = name
        self._fabric = fabric
        self._solver = solver

        angles = [0, 90, 180, 270]
        for angle in angles:
            attrName = '_rot' + str(angle)
            varName  = self.name + attrName
            var = solver.declare_const(varName, solver.Bool)
            setattr(self, attrName, var)

    @property
    def name(self):
        return self._name

    @property
    def fabric(self):
        return self._fabric

    @property
    def solver(self):
        return self._solver

    def rot(self, deg):
        return getattr(self, '_rot'+str(deg))

    @property
    def allBits(self):
        return [self.rot(deg) for deg in [0, 90, 180, 270]]

    @property
    def invariants(self):
        return self.solver.ExactlyOne(self.allBits)

    def decode(self):
        for deg in [0, 90, 180, 270]:
            if self.solver.get_value(self.rot(deg)).as_bool():
                return radians(deg)
        raise Exception('Invalid angle.')

    def equals(self, theta):
        constraints = self.solver.EmptyConstraint()

        for deg in [0, 90, 180, 270]:
            if deg == round(degrees(theta)):
                constraints.add(self.solver.IsTrue(self.rot(deg)))
            else:
                constraints.add(self.solver.IsFalse(self.rot(deg)))

        return constraints

class Layer2:
    def __init__(self, name, fabric, solver):
        self._name = name
        self._fabric = fabric
        self._solver = solver
        self._layer = solver.declare_const(self.name + '_layer', solver.Bool)

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
    def layer(self):
        return self._layer

    @property
    def invariants(self):
        return self.solver.EmptyConstraint()

    def equals(self, other):
        if other:
            return self.solver.IsTrue(self.layer)
        else:
            return self.solver.IsFalse(self.layer)

    def decode(self):
        return self.solver.get_value(self.layer).as_bool()

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

class Base2H(PositionBase):
    '''
    Base class for 2 hot representations
    '''

    def __init__(self, name, fabric, solver):
        super().__init__(name, fabric, solver)

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
        return self.solver.theory_const(sorts.BitVec(self.fabric.cols), 2**x)

    def encode_y(self, y):
        return self.solver.theory_const(sorts.BitVec(self.fabric.rows), 2**y)

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
    
        self._x = solver.declare_const(self.name + '_x', sorts.BitVec(self._x_bits))
        self._y = solver.declare_const(self.name + '_y', sorts.BitVec(self._y_bits))

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
        bvult = functions.bvult()
        constraint = []
        if self._is_x_pow2:
            ix = self._x_bits - 1
            ext = functions.extract(ix, ix)
            constraint.append(ext(self.x) == 0)
        else:
            constraint.append(bvult(self.x, self.fabric.cols))
        if self._is_y_pow2:
            iy = self._y_bits - 1
            ext = functions.extract(iy, iy)
            constraint.append(ext(self.y) == 0)
        else:
            constraint.append(bvult(self.y, self.fabric.rows))
        return And(constraint)

    def get_coordinates(self):
        return (self.solver.get_value(self.x).as_int(), self.solver.get_value(self.y).as_int())

    def encode(self, p):
        return self.encode_x(p[0]), self.encode_y(p[1])

    def encode_x(self, x):
        return self.solver.theory_const(sorts.BitVec(self._x_bits), x)

    def encode_y(self, y):
        return self.solver.theory_const(sorts.BitVec(self._y_bits), y)
