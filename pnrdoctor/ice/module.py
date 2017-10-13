from enum import Enum, Flag, auto
from pnrdoctor.util import NamedIDObject, BiDict, BiMultiDict
from .net import Tie
from .fabric import Fabric

__all__ = ['IceModule']

Resource = Fabric.Resource

class Module(NamedIDObject):
    def __init__(self, name, resource=Resource.UNSET ,attributes=dict()):
        super().__init__(name)
        self._inputs = BiDict()
        self._outputs = BiMultiDict()
        self.resource = resource

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
        assert port not in self._inputs, \
          'Input should never have more than one driver. Use fuse_reg to replace a register input.'
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

