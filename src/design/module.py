from util import NamedIDObject

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
    
    def op_atr(self):
        return self._op_atr
    
    def _add_input(self, src, port):
        self._inputs[port] = src

    def _add_output(self, dst, port):
        self._outputs[port] = dst

        
    def __repr__(self):
        return self.name
        #return 'name: {}, inputs: {}, outputs: {}'.format(self.name, {x.src.name for x in self.inputs.values()}, {x.dst.name for x in self.outputs.values()})


