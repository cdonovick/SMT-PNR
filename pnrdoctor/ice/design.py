from pnrdoctor.util import IDObject, NamedIDObject, SortedDict
from .module import Module
from .net    import Net,Tie

class Design(NamedIDObject):
    def __init__(self, mods, nets, name=''):
        super().__init__(name)
        ties = set(nets.keys())

        _mods = dict()
        for mod_name, args in mods.items():
            mod = Module(mod_name)
            mod.resource = args['res']
            mod.type_ = args['type']
            mod.blif = args['blif']
            _mods[mod_name] = mod

        mods = _mods


        _nets = dict()
        _ties = set()
        for net_name in nets:
            ties = set()
            for src_name, src_port, dst_name, dst_port, width in nets[net_name]:
                src = mods[src_name]
                dst = mods[dst_name]
                ties.add(Tie(src, src_port, dst, dst_port, width))
            _ties = _ties.union(ties)
            _nets[net_name] = Net(net_name, ties)

        self._modules = frozenset(mods.values())
        self._ties = frozenset(_ties)
        self._nets = frozenset(_nets.values())

    @property
    def modules(self):
        return self._modules

    @property
    def ties(self):
        return self._ties

    @property
    def nets(self):
        return self._nets

