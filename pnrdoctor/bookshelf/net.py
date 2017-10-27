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
        return self.module.port_info[self.port]


    def __repr__(self):
        return '{} :{}:{} ({})'.format(self.net, self.module, self.port, self.port_info)

class Net(NamedIDObject):
    def __init__(self, name, ends):
        super().__init__(name)
        self._binds=frozenset(map(lambda e : Bind(*e, self), ends))
        self._modules=frozenset(map(lambda x : x.module, self.binds)) 
        self._is_clock = any(b.port_info[1] == 'CLOCK' for b in self.binds)
        self._is_ctrl  = any(b.port_info[1] == 'CTRL'  for b in self.binds)
        self._is_sig   = all(b.port_info[1] == 'SIG'   for b in self.binds)
        
        self.num_dri = sum(b.port_info[0] == 'OUTPUT' for b in self.binds) 
        self.num_rec = sum(b.port_info[0] == 'INPUT' for b in self.binds) 


    @property
    def binds(self):
        return self._binds

    @property
    def modules(self):
        return self._modules

    @property    
    def is_clock(self):
        return self._is_clock

    @property
    def is_ctrl(self):
        return self._is_clock

    @property
    def is_sig(self):
        return self._is_sig

    def __len__(self):
        return len(self.binds)
