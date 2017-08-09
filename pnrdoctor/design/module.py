from enum import Enum

from pnrdoctor.util import NamedIDObject
from pnrdoctor.util import BiMultiDict

class Module(NamedIDObject):
    def __init__(self, name, attributes=dict()):
        super().__init__(name)
        self._inputs = BiMultiDict()
        self._outputs = BiMultiDict()
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

    def __str__(self):
        return '{}: {} {} {}'.format(self.name, self.inputs, self.outputs, self.resource)

class Resource(Enum):
    UNSET = 0
    PE    = 1
    Mem   = 2
    IO    = 1 #HACK: IO uses PE
    Reg   = 4
    Fused = 5
    # For fabric actually
    # Eventually we should move this
    SB    = 6
    CB    = 7
