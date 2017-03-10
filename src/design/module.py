from util import NamedIDObject

class Module(NamedIDObject):
    def __init__(self, name, op, inputs=(), outputs=()):
        super().__init__(name)
        self._op = op
        self._inputs = set(inputs)
        self._outputs = set(outputs)

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

    def _add_input(self, src):
        self._inputs.add(src)

    def _add_output(self, dst):
        self._outputs.add(dst)

        
    def __repr__(self):
        return 'name: {}, inputs: {}, outputs: {}'.format(self.name, {x.src.name for x in self.inputs}, {x.dst.name for x in self.outputs})


