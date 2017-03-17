from util import NamedIDObject

class Module(NamedIDObject):
    def __init__(self, name, op):
        super().__init__(name)
        self._op = op
        self._inputs = dict()
        self._outputs = dict()

    @property
    def inputs(self):
        '''
            returns a iterator over Wires
        '''
        return iter(self._inputs)

    @property
    def outputs(self):
        '''
            returns a iterator over Wires
        '''
        return iter(self._outputs)

    @property
    def op(self):
        return self._op

    def _add_input(self, src, port):
        self._inputs[port] = src

    def _add_output(self, dst, port):
        self._outputs[port] = dst

        
    def __repr__(self):
        return 'name: {}, inputs: {}, outputs: {}'.format(self.name, {x.src.name for x in self.inputs.values()}, {x.dst.name for x in self.outputs.values()})


