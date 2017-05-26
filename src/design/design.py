'''
    Classes for represtenting designs and various constructors
'''
from util import NamedIDObject, SortedDict
from .module import Module
from .net import Net

_fusable = {(s, d) for s in ('Reg', 'Const') for d in ('PE',)}
class Design(NamedIDObject):
    def __init__(self, modules, nets, name=''):
        super().__init__(name)
        self._modules = set()
        self._nets = set()
        self._v_net_cache = dict()

        mods = SortedDict()
        for mod_name,args in modules.items():
            mod = Module(mod_name)
            mod.type_ = args['type']
            mod.fused = False
            if args['conf'] is not None:
                mod.config = args['conf']

            if mod.type_ in ('PE', 'IO'):
                mod.resource = 'PE'
            else:
                mod.resource = mod.type_

            self.modules.add(mod)
            mods[mod_name] = mod

        for src_name, src_port, dst_name, dst_port, width in nets:

            src = mods[src_name]
            dst = mods[dst_name]
            if (src.type_, dst.type_) in _fusable:
                src.fused = True
                src.resource = None

            self.nets.add(Net(src, src_port, dst, dst_port, width))

    @property
    def modules(self):
        return self._modules

    @property
    def nets(self):
        return self._nets


    @property
    def nf_modules(self):
        yield from filter(lambda x : not x.fused, self.modules)

    @property
    def f_modules(self):
        yield from filter(lambda x : x.fused, self.modules)

    @property
    def virtual_nets(self):
        nets = set((n.src, n.src_port, n.dst, n.dst_port, n.width, 0)
                for n in self.nets
                if (n.src.type_ != 'Reg'  and n.src.type_ != 'Const'))
        while nets:
            n = nets.pop()
            if n[2].type_ != 'Reg':
                assert n[2].type_ != 'Const', "Const cannot be dst"
                try:
                    yield self._v_net_cache[n]
                except KeyError:
                    t = Net(*n[:-1])
                    t.length = n[-1]
                    self._v_net_cache[n] = t
                    yield t
            else:
                for dst_net in n[2].outputs.values():
                    assert dst_net.width == n[4]
                    #print("Fusing ({a}->{b}), ({b}->{c}) to ({a}->{c})".format(a=n[0].name, b=n[2].name, c=dst_net.dst.name))
                    nets.add((n[0], n[1], dst_net.dst, dst_net.dst_port, n[4], n[5] + (0 if n[2].fused else 1)))

