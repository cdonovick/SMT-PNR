'''
    Classes for represtenting designs and various constructors
'''
from util import NamedIDObject, SortedDict
from .module import Module
from .net import Net

class Design(NamedIDObject):
    def __init__(self, modules, nets, name=''):
        super().__init__(name)
        self._modules = set()
        self._nets = set()

        mods = SortedDict()
        for mod_name,args in modules.items():
            mod = Module(mod_name, args['type'], args['conf'])
            self.modules.add(mod)
            mods[mod_name] = mod

        for src_name, src_port, dst_name, dst_port, width in nets:
            src = mods[src_name]
            dst = mods[dst_name]
            self.nets.add(Net(src, src_port, dst, dst_port, width))

    @property
    def modules(self):
        return self._modules

    @property
    def nets(self):
        return self._nets


