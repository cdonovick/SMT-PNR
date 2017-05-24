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


