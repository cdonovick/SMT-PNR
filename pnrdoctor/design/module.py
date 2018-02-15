from enum import Enum, Flag, auto
from pnrdoctor.util import NamedIDObject, BiDict, BiMultiDict
from .net import Tie

class Module(NamedIDObject):
    def __init__(self, name, attributes=dict()):
        super().__init__(name)
        self._inputs = BiDict()
        # outputs should be a BiMultiDict to support fanout
        self._outputs = BiMultiDict()
        self._resource = Resource.UNSET
        self._registered_ports = set()
        self._layer = Layer.UNSET

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

    def add_registered_input(self, port):
        assert port in self._inputs
        self._registered_ports.add(port)

    @property
    def registered_ports(self):
        return self._registered_ports

    @property
    def resource(self):
        return self._resource

    @resource.setter
    def resource(self, res):
        if isinstance(res, Resource):
            self._resource = res
        else:
            raise TypeError('Expected Resource not {}'.format(type(res)))

    @property
    def layer(self):
        return self._layer

    @layer.setter
    def layer(self, layer):
        if isinstance(layer, Layer):
            self._layer = layer
        else:
            raise TypeError('Expected Layer not {}'.format(type(layer)))

    def __str__(self):
        return '{}: {} {} {}'.format(self.name, self.inputs, self.outputs, self.resource)

    def fuse_reg(self, port):
        '''
           Fuses the register at the given port and returns the new tie
        '''
        tie = self._inputs[port]
        src = tie.src

        if tie.fused_reg:
            raise ValueError('Cannot have two fused regs on a tie')

        assert tie.src.resource in {Resource.Reg, Resource.Fused}, \
          "Only registers are fused onto a tie (Consts keep their ties)"

        assert len(src.inputs) == 1, \
          "Can't collapse an input whose source has > 1 inputs and " + \
          "this tie's src has {} inputs".format(len(src.inputs))

        input_tie = next(iter(src.inputs.values()))
        new_src = input_tie.src

        del self._inputs[port]

        if input_tie in new_src.outputs.I:
            # this tie could have already been removed in a previous
            # call to collapse_input
            del new_src.outputs.I[input_tie]

        assert input_tie.width == tie.width, \
          "Can't collapse input with different width"

        new_tie = Tie(new_src, input_tie.src_port, self, port, tie.width)

        new_tie.fused_reg = True

        return new_tie


class Resource(Enum):
    UNSET = 0
    PE    = 1
    Mem   = 2
    IO    = 3
    Reg   = 4
    Fused = 5
    # For fabric actually
    # Eventually we should move this
    SB    = 6
    CB    = 7
    EMPTY = 8

class Layer(Flag):
    UNSET    = 0
    Data     = auto()
    Bit      = auto()
    Combined = Data | Bit

    @classmethod
    def width_to_layer(cls, w):
        if w == 1:
            return cls.Bit
        if w == 16:
            return cls.Data

        raise ValueError('No layer for width: {}'.format(w))

    @property
    def width(self):
        if self is type(self).Bit:
            return 1
        if self is type(self).Data:
            return 16

        raise ValueError('No width for layer: {}'.format(self))

# For now, ties and routing still use 1/16 instead of Bit/Data
# This is used in pnr/constraints to do this conversion
# Eventually everything will be moved to Layer
layer2widths = {Layer.Data: {16}, Layer.Bit: {1}, Layer.Combined: {1, 16}}
