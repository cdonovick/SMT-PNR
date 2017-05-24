from util import NamedIDObject

class Module(NamedIDObject):
    def __init__(self, name, type_, config):
        super().__init__(name)
        self._type_ = type_
        self._config = config
        self._inputs = dict()
        self._outputs = dict()

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

    @property
    def type_(self):
        return self._type_

    @property
    def config(self):
        return self._config

    def _add_input(self, src, port):
        self._inputs[port] = src

    def _add_output(self, dst, port):
        self._outputs[port] = dst
