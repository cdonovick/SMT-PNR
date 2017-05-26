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
            if (src.type_, dst.type_) in _fusable:
                src.fused = True
                src.resource = None

            idx = (src, src_port, dst, dst_port, width)

            _nets[idx] = Net(*idx)
            #for virtual nets
            if src.type_ != 'Reg' and src.type_ != 'Const':
                idx_set.add(idx + (0,))
        
        self._nets=frozenset(_nets.values())

        #build _v_nets
        _v_nets = set()
        while idx_set:
            idx = idx_set.pop()
            #idx[2] == dst
            if idx[2].type_ != 'Reg':
                assert idx[2].type_ != 'Const', 'Const cannot be a sink'
                #[:-1] are constructor args, [-1] is num_reg
                if idx[:-1] in _nets:
                    assert idx[-1] == 0, 'Non-virtual net with register'
                    _v_nets.add(_nets[idx[:-1]])
                else:
                    t = Net(*idx[:-1])
                    t.num_reg = idx[-1]
                    _v_nets.add(t)
            else:
                for dst_net in idx[2].outputs.values():
                    assert dst_net.width == idx[4] 
                    #print("Fusing ({a}->{b}), ({b}->{c}) to ({a}->{c})".format(a=idx[0].name, b=idx[2].name, c=dst_net.dst.name))
                    idx_set.add((idx[0], idx[1], dst_net.dst, dst_net.dst_port, idx[4], idx[5] + (0 if idx[2].fused else 1)))
        
        self._v_nets = frozenset(_v_nets)

    @property
    def modules(self):
        return self._modules

    @property
    def nets(self):
        return self._nets

    @lru_cache(maxsize=32)
    def modules_with_attr(self, attr):
        return set(filter(lambda x : hasattr(x, attr), self.modules))

    @lru_cache(maxsize=32)
    def modules_with_attr_val(self, attr, val):
        return set(filter(lambda x : hasattr(x, attr) and getattr(x, attr) == val, self.modules))


    @property
    def virtual_nets(self):
        return self._v_nets

