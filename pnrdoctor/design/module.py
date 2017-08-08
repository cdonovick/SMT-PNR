from enum import Enum
from pnrdoctor.util import NamedIDObject, BiDict, BiMultiDict
from .net import Tie

class Module(NamedIDObject):
    def __init__(self, name, attributes=dict()):
        super().__init__(name)
        self._inputs = BiDict()
        # outputs should be a BiMultiDict to support fanout
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
        assert port not in self._inputs, \
          'Input should never have more than one driver. Use collapse_input to replace an input'
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

    def collapse_input(self, idx):
        if idx in self._inputs:
            dst_port = idx
            tie = self._inputs[idx]
        elif idx in self._inputs.I:
            # idx is a tie
            tie = idx

            # get the "forward representation" index
            dst_port = self._inputs.I[idx]
        else:
            raise KeyError('{} does not seem to be a key or value in outputs'.format(idx))

        src = tie.src
        assert len(src.inputs) == 1, \
          "Can't collapse an input whose source has > 1 inputs and this tie's src has {} inputs".format(len(src.inputs))

        input_tie = next(iter(src.inputs.values()))
        new_src = input_tie.src

        del self._inputs[dst_port]

        if input_tie in new_src.outputs.I:
            # this tie could have already been removed in a previous call
            # to collapse_input
            del new_src.outputs.I[input_tie]

        assert input_tie.width == tie.width, \
          "Can't collapse input with different width"

        new_tie = Tie(new_src, input_tie.src_port, self, dst_port, tie.width)

        # if there's a fused reg anywhere on the path, then it should
        # carry through
        new_tie.fused_reg = input_tie.fused_reg | tie.fused_reg

        if src.resource == Resource.Fused:
            new_tie.fused_reg = True
        elif src.resource == Resource.Reg:
            if len(input_tie.regs) > 0:
                front_ties = input_tie.regs
            else:
                front_ties = [input_tie]

            if len(tie.regs) > 0:
                rear_ties = tie.regs
            else:
                rear_ties = [tie]

            new_tie.regs = front_ties + rear_ties
        else:
            raise NotImplementedError("Unhandled case in collapse_input")

        return new_tie

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
