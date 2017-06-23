'''
    Classes for represtenting designs and various constructors
'''
from collections import defaultdict
from util import NamedIDObject, SortedDict
from .module import Module, Resource
from .net import Net
from functools import lru_cache

_fusable = {(s, d) for s in ('Reg', 'Const') for d in ('PE',)}
class Design(NamedIDObject):
    def __init__(self, modules, nets, name=''):
        super().__init__(name)
        _mods = SortedDict()
        _nets = dict()

        # HACK to make only one wire leave input
        # to help CGRA team with io hack
        # creating a dummy PE (i.e. input + 0)

        # find input modules
        inputmods = defaultdict(int)
        for src_name, src_port, dst_name, dst_port, width in nets:
            if modules[src_name]['type'] == 'IO':
                #an output should never be a src
                assert modules[src_name]['conf'] == 'i'
                inputmods[src_name] += 1

        #filter the inputs for inputs with more than one input
        inputmods = {k for k,v in inputmods.values() if v > 1}

        #we need to hack some inputs
        if inputmods:
            #create const_0 module
            const_0_name = '__HACK__io_const_0'
            assert const_0_name  not in modules, 'Hack name ({}) in use things are going to break'.format(const_0_name)
            modules[const_0_name] = {
                    'type' : 'Const',
                    'conf' : 0,
                    'res'  : Resource.UNSET,
                }

            #change all the mods to be adders
            for mod_name in inputmods:
                saved_args = modules[mod_name].copy()
                modules[mod_name]['type'] = 'PE'
                modules[mod_name]['conf'] = 'add'
                modules[mod_name]['res']  = Resource.PE

                hack_io_name = '__HACK__' + mod_name
                assert hack_io_name not in modules, 'Hack name ({}) in use things are going to break'.format(hack_io_name)

                #make a hack mod
                modules[hack_io_name] = saved_args

                #make a net from the hack mod to original io (the now adder)
                #assuming 16 width but we are fucked if its not anyway as the adder trick wont work
                nets.add((hack_io_name, 'pe_out_res', mod_name, 'a', 16))
                #make a net from the const 0 to original io (the now adder)
                nets.add((const_0_name, 'out', mod_name, 'b', 16))

        # end HACK for IOs


        #build modules
        for mod_name,args in modules.items():
            mod = Module(mod_name)
            mod.type_ = args['type']
            if args['conf'] is not None:
                mod.config = args['conf']

            mod.resource = args['res']
            _mods[mod_name] = mod

        self._modules=frozenset(_mods.values())

        fuse_me = set()
        fuse_no = set()

        #build nets
        for src_name, src_port, dst_name, dst_port, width in nets:

            src = _mods[src_name]
            dst = _mods[dst_name]
            idx = (src, src_port, dst, dst_port, width)

            if (src.type_, dst.type_) in _fusable:
                fuse_me.add(src)
            else:
                fuse_no.add(src)


            _nets[idx] = Net(*idx)

        self._nets=frozenset(_nets.values())
        #build _p_modules
        _p_modules = set()
        for m in self.modules:
            if m in fuse_no or m not in fuse_me:
                _p_modules.add(m)
            else:
                assert m in fuse_me
                m.resource = Resource.Fused

        self._p_modules = frozenset(_p_modules)


        # build _p_nets
        _p_nets = set()
        _net_cache = _nets.copy()
        while _nets:
            _, net = _nets.popitem()
            if net.src.resource == Resource.Fused:
                # handle this when it's a destination
                continue
            elif net.dst.resource != Resource.Fused:
                _p_nets.add(net)
            else:
                # fuse nets with a fused dst
                for dst_net in net.dst.outputs.values():
                    idx = net.src, net.src_port, dst_net.dst, dst_net.dst_port, net.width
                    #print("Fusing: \n({a}  ->  {b})\n ({b}  ->  {c})\n({a}  ->  {c})\n".format(a=idx[0].name, b=idx[2].name, c=dst_net.dst.name))
                    assert dst_net.width == net.width
                    assert idx not _net_cache
                    new_net = Net(*idx)
                    _nets[idx] = new_net
                    _net_cache[idx] = new_net


        self._p_nets = frozenset(_p_nets)

        for module in self.modules:
            assert module.resource != Resource.UNSET

        for module in self.physical_modules:
            assert module.resource != Resource.Fused

        for net in self.physical_nets:
            assert net.src.resource != Resource.Fused, 'src'
            assert net.dst.resource != Resource.Fused, 'dst'

        for net in self.nets:
            assert (net in self.physical_nets) or (net.src.resource == Resource.Fused) or (net.dst.resource == Resource.Fused)

        for module in self.modules:
            if module.resource == Resource.Fused:
                assert module not in self.physical_modules
            else:
                assert module in self.physical_modules, module


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
    def physical_nets(self):
        return self._p_nets

    @property
    def physical_modules(self):
        return self._p_modules
