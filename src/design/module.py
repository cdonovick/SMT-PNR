from util import NamedIDObject

import numpy as np
from math import cos, sin

class Shape:
    def __init__(self, points):
        self._points = points

    @property
    def points(self):
        return self._points

    def rotate(self, th):
        M = np.matrix([[ cos(th), -sin(th)],
                       [ sin(th),  cos(th)]])
        return Shape(M*self.points)
    
    @property
    def xmin(self):
        return np.min(self.points[0]).item()

    @property
    def xmax(self):
        return np.max(self.points[0]).item()

    @property
    def ymin(self):
        return np.min(self.points[1]).item()

    @property
    def ymax(self):
        return np.max(self.points[1]).item()

class RectShape(Shape):
    def __init__(self, w, h):
        points = np.matrix([[0, 0, w, w],
                            [0, h, h, 0]])
        super().__init__(points)

class PcbModule(NamedIDObject):
    def __init__(self, name, width, height, x, y, theta, mirror, pinned):
        super().__init__(name)
    
        self._width = width
        self._height = height
        self._x = x
        self._y = y
        self._theta = theta
        self._mirror = mirror
        self._pinned = pinned
        self._shape = RectShape(width, height)

    @property
    def width(self):
        return self._width

    @property
    def height(self):
        return self._height

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @property
    def theta(self):
        return self._theta

    @property
    def mirror(self):
        return self._mirror

    @property
    def pinned(self):
        return self._pinned
        
    @property
    def shape(self):
        return self._shape

class Module(NamedIDObject):
    def __init__(self, name, op, op_val, op_atr):
        super().__init__(name)
        self._op = op
        self._op_val = op_val
        self._op_atr = op_atr
        self._inputs = dict()
        self._outputs = dict()

    @property
    def inputs(self):
        '''
            returns a iterator over Wires
        '''
        return self._inputs.values()

    @property
    def outputs(self):
        '''
            returns a iterator over Wires
        '''
        return self._outputs.values()

    @property
    def op(self):
        return self._op

    @property
    def op_val(self):
        return self._op_val
    
    @property
    def op_atr(self):
        return self._op_atr
    
    def _add_input(self, src, port):
        self._inputs[port] = src

    def _add_output(self, dst, port):
        self._outputs[port] = dst

        
    def __repr__(self):
        return self.name
        #return 'name: {}, inputs: {}, outputs: {}'.format(self.name, {x.src.name for x in self.inputs.values()}, {x.dst.name for x in self.outputs.values()})


