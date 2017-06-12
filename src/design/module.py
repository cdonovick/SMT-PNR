from util import NamedIDObject
from enum import Enum

class Module(NamedIDObject):
    def __init__(self, name, attributes=dict()):
        super().__init__(name)
        self._inputs = dict()
        self._outputs = dict()
        self._resource = Resource.UNSET

    @property
    def inputs(self):
        '''
            returns a iterator over Wires
        '''
        return self._inputs

    @property
    def outputs(self):
        '''
            returns a iterator over Wires
        '''
        return self._outputs


    def _add_input(self, src, port):
        self._inputs[port] = src

    def _add_output(self, dst, port):
        self._outputs[port] = dst

    @property
    def resource(self):
        return self._resource

    @resource.setter
    def resource(self, res):
        if isinstance(res, Resource):
            self._resource = res
        else:
            raise TypeError('Expected Resource not {}'.format(type(res)))

class Resource(Enum):
    UNSET = 0
    PE    = 1
    Mem   = 2
    IO    = 1 #HACK: IO uses PE
    Reg   = 4
    Fused = 5
