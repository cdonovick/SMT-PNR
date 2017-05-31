'''
    Classes for represtenting designs and various constructors
'''
from util import NamedIDObject, SortedDict
from .module import Module
from .net import Net
from functools import lru_cache

_fusable = {(s, d) for s in ('Reg', 'Const') for d in ('PE',)}
class Design(NamedIDObject):
    def __init__(self, modules, nets, name=''):
        super().__init__(name)
        _mods = SortedDict()
        _nets = dict()

    
        #build modules
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

            _mods[mod_name] = mod

        self._modules=frozenset(_mods.values())

        #build nets
        idx_set = set()
        for src_name, src_port, dst_name, dst_port, width in nets:

            src = _mods[src_name]
            dst = _mods[dst_name]
            idx = (src, src_port, dst, dst_port, width)

            if (src.type_, dst.type_) in _fusable:
                src.fused = True
                src.resource = None
            else:
                #for virtual nets
                idx_set.add(idx)


            _nets[idx] = Net(*idx)
        
        self._nets=frozenset(_nets.values())

        #build _v_nets
        _v_nets = set()
        while idx_set:
            idx = idx_set.pop()
            #idx[2] == dst
            if not idx[2].fused:
                if idx in _nets:
                    _v_nets.add(_nets[idx])
                else:
                    t = Net(*idx)
                    _v_nets.add(t)
            else:
                for dst_net in idx[2].outputs.values():
                    assert dst_net.width == idx[4] 
                    #print("Fusing ({a}->{b}), ({b}->{c}) to ({a}->{c})".format(a=idx[0].name, b=idx[2].name, c=dst_net.dst.name))
                    idx_set.add((idx[0], idx[1], dst_net.dst, dst_net.dst_port, idx[4]))
        self._v_nets = frozenset(_v_nets)

    @property
    def modules(self):
        return self._modules

    @property
    def nets(self):
        return self._nets

    @lru_cache(maxsize=32)
    def modules_with_attr(self, attr):
        return frozenset(filter(lambda x : hasattr(x, attr), self.modules))

    @lru_cache(maxsize=32)
    def modules_with_attr_val(self, attr, val):
        return frozenset(filter(lambda x : hasattr(x, attr) and getattr(x, attr) == val, self.modules))

    @property
    def virtual_nets(self):
        return self._v_nets

