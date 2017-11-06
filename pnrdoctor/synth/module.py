from pnrdoctor.util import NamedIDObject, BiDict, BiMultiDict


class Module(NamedIDObject):
    def __init__(self, name, i_ports, o_ports):
        super().__init__(name)
        self._inputs = BiDict()
        self._outputs = BiMultiDict()
        self._i_ports = frozenset(i_ports)
        self._o_ports = frozenset(o_ports)


    @property
    def ports(self):
        return self._i_ports | self._o_ports
 
    @property
    def i_ports(self):
        return self._i_ports

    @property
    def o_ports(self):
        return self._o_ports

    @property
    def inputs(self):
        return self._inputs

    @property
    def outputs(self):
        return self._outputs

    def _add_input(self, port, net):
        assert port in self.i_ports, (port, self.i_ports)
        self._inputs[port] = net

    def _add_output(self, port, net):
        assert port in self.o_ports, (port, self.o_ports)
        self._outputs[port] = net   

    def __str__(self):
        return '{}: {} {}'.format(self.name, self.kind, self.resource)

