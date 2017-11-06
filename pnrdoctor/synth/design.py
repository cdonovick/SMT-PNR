from itertools import starmap
from pnrdoctor.util import IDObject, NamedIDObject, SortedDict
from .module import Module
from .net    import Net, Connection

class Design(NamedIDObject):
    def __init__(self, mods, nets, name=''):
        super().__init__(name)

        _mods = dict()
        for mod_name, args in mods.items():
            _mods[mod_name] = Module(mod_name, args['i_ports'], args['o_ports'], )

        mods = _mods

        _nets = set()

        for net_name, args in nets.items():
            src = Connection(mods[args['src']['module']], args['src']['port'])
            dsts = set()
            for c in args['dsts']:
                dsts.add(Connection(mods[c['module']], c['port']))    
            _nets.add(Net(net_name, src, dsts))

        nets = _nets
        
        for n in nets:
            src = n.src
            src.module._add_output(src.port, n)
            for dst in n.dsts:
                dst.module._add_input(dst.port, n)

        self._modules = frozenset(mods.values())
        self._nets = frozenset(_nets)


    @property
    def modules(self):
        return self._modules

    @property
    def nets(self):
        return self._nets

    @property
    def ties(self):
        for n in self.nets:
            yield from n.ties


