from util import NamedIDObject

class Module(NamedIDObject):
    def __init__(self, name, attributes=dict()):
        super().__init__(name)
        self._inputs = dict()
        self._outputs = dict()
        self._attributes = attributes

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
    def attributes(self):
        return self._attributes

    def __getitem__(self, key):
        return self.attributes[key]

    def __setitem__(self, key, value):
        self.attributes[key] = value

    def _add_input(self, src, port):
        self._inputs[port] = src

    def _add_output(self, dst, port):
        self._outputs[port] = dst
