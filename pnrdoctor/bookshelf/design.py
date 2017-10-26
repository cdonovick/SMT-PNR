from itertools import starmap
from pnrdoctor.util import IDObject, NamedIDObject, SortedDict
from .module import Module
from .net    import Net

class Design(NamedIDObject):
    def __init__(self, mods, nets, name=''):
        super().__init__(name)
        ties = set(nets.keys())

        _mods = dict()
        for mod_name, args in mods.items():
            _mods[mod_name] = Module(mod_name, args['kind'], args['res'], args['ports'])

        mods = _mods

        _nets = set()
        for net_name, ends in nets.items():
            _nets.add(Net(net_name, ((mods[i], p) for i,p in ends)))

        self._modules = frozenset(mods.values())
        self._nets = frozenset(_nets)

    @property
    def modules(self):
        return self._modules

    @property
    def nets(self):
        return self._nets

