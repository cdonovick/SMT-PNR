from itertools import starmap
from pnrdoctor.util import IDObject, NamedIDObject


class Bind:
    def __init__(self, module, port, net):
        module._add_connection(port, net)
        self._module = module
        self._net = net
        self._port = port

    @property
    def module(self):
        return self._module

    @property
    def net(self):
        return self._net

    @property
    def port(self):
        return self._port

    @property
    def port_info(self):
        return self.terminal.port_info[self.port]



class Net(NamedIDObject):
    def __init__(self, name, ends):
        super().__init__(name)
        self._binds=frozenset(map(lambda e : Bind(*e, self), ends))

    @property
    def binds(self):
        return self._binds

    @property
    def terminals(self):
        return map(lambda x : x.terminal, self.binds)
