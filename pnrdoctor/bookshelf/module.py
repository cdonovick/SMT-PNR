from enum import Enum, Flag, auto
from pnrdoctor.util import NamedIDObject, BiDict, BiMultiDict

class Module(NamedIDObject):
    def __init__(self, name, kind, resource, port_info):
        super().__init__(name)
        self._port_info = port_info
        self._ports = BiMultiDict()
        self._kind = kind
        self._resource = resource

    @property
    def port_info(self):
        return self._port_info

    @property
    def ports(self):
        return self._ports

    def _add_connection(self, port, net):
        assert port in self._port_info
        self.ports[port] = net

    @property
    def kind(self):
        return self._kind

    @property
    def resource(self):
        return self._resource

    def __str__(self):
        return '{}: {} {}'.format(self.name, self.kind, self.resource)

