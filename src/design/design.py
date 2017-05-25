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

        mods = SortedDict()
        for mod_name,args in modules.items():
            mod = Module(mod_name)
            mod['type'] = args['type']
            mod['fused'] = False
            if args['conf'] is not None:
                mod['config'] = args['conf']

            if args['type'] in ('PE', 'IO'):
                mod['resource'] = 'PE'
            else:
                mod['resource'] = args['type']

            self.modules.add(mod)
            mods[mod_name] = mod

        for src_name, src_port, dst_name, dst_port, width in nets:

            src = mods[src_name]
            dst = mods[dst_name]
            if (src['resource'], dst['resource']) in _fusable:
                src['fused'] = True
                src['resource'] = None
            
            self.nets.add(Net(src, src_port, dst, dst_port, width))

    @property
    def modules(self):
        return self._modules

    @property
    def nets(self):
        return self._nets


    @property
    def nf_modules(self):
        yield from filter(lambda x : not x['fused'], self.modules)

    @property
    def f_modules(self):
        yield from filter(lambda x : x['fused'], self.modules)

    @property
    def virtual_nets(self):
        s = set()
        for net in self.nets:
            if net.src['fused']:
                src_s = (x for x in net.src.inputs.values())
            else:
                src_s = (net,)

            if net.dst['fused']:
                dst_s = (x for x in net.dst.outputs.values())
            else:
                dst_s = (net,)

            for s_net in src_s:
                for d_net in dst_s:
                    assert s_net.width == d_net.width
                    assert not s_net.src['fused']
                    assert not d_net.dst['fused']
                    yield Net(s_net.src, s_net.src_port, d_net.dst, d_net.dst_port, s_net.width)

