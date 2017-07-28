'''
    Classes for represtenting designs and various constructors
'''
from collections import defaultdict
from functools import lru_cache

from pnrdoctor.util import NamedIDObject, SortedDict
from .module import Module, Resource
from .net import Net, Tie
from functools import lru_cache

_fusable = {(s, d) for s in ('Reg', 'Const') for d in ('PE',)}
class Design(NamedIDObject):
    def __init__(self, modules, ties, name=''):
        super().__init__(name)
        _mods = SortedDict()
        _ties = dict()

        # HACK to make only one wire leave input
        # to help CGRA team with io hack
        # creating a dummy PE (i.e. input + 0)

        # find input modules
        inputmods = defaultdict(int)
        for src_name, src_port, dst_name, dst_port, width in ties:
            if modules[src_name]['type'] == 'IO':
                #an output should never be a src
                assert modules[src_name]['conf'] == 'i'
                inputmods[src_name] += 1

        #filter the inputs for inputs with more than one input
        inputmods = {k for k,v in inputmods.items() if v > 1}

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

                #make a tie from the hack mod to original io (the now adder)
                #assuming 16 width but we are fucked if its not anyway as the adder trick wont work
                ties.add((hack_io_name, 'pe_out_res', mod_name, 'a', 16))
                #make a tie from the const 0 to original io (the now adder)
                ties.add((const_0_name, 'out', mod_name, 'b', 16))

        # end HACK for IOs


        #build modules
        for mod_name, args in modules.items():
            mod = Module(mod_name)
            mod.type_ = args['type']
            if args['conf'] is not None:
                mod.config = args['conf']

            mod.resource = args['res']
            _mods[mod_name] = mod

        self._modules=frozenset(_mods.values())

        fuse_me = set()
        fuse_no = set()

        #build ties
        for src_name, src_port, dst_name, dst_port, width in ties:

            src = _mods[src_name]
            dst = _mods[dst_name]
            idx = (src, src_port, dst, dst_port, width)

            if (src.type_, dst.type_) in _fusable:
                fuse_me.add(src)
            else:
                fuse_no.add(src)


            _ties[idx] = Tie(*idx)

        self._ties=frozenset(_ties.values())
        #build _p_modules
        _p_modules = set()
        for m in self.modules:
            if m in fuse_no or m not in fuse_me:
                _p_modules.add(m)
            else:
                assert m in fuse_me
                m.resource = Resource.Fused

        self._p_modules = frozenset(_p_modules)


        # build _p_ties
        _p_ties = set()
        _tie_cache = _ties.copy()
        while _ties:
            _, tie = _ties.popitem()
            if tie.src.resource == Resource.Fused:
                # handle this when it's a destination
                continue
            elif tie.dst.resource != Resource.Fused:
                _p_ties.add(tie)
            else:
                # fuse ties with a fused dst
                for dst_tie in tie.dst.outputs.values():
                    idx = tie.src, tie.src_port, dst_tie.dst, dst_tie.dst_port, tie.width
                    #print("Fusing: \n({a}  ->  {b})\n ({b}  ->  {c})\n({a}  ->  {c})\n".format(a=idx[0].name, b=idx[2].name, c=dst_tie.dst.name))
                    assert dst_tie.width == tie.width
                    assert idx not in _tie_cache
                    new_tie = Tie(*idx)
                    _ties[idx] = new_tie
                    _tie_cache[idx] = new_tie


        self._p_ties = frozenset(_p_ties)

        for module in self.modules:
            assert module.resource != Resource.UNSET

        for module in self.physical_modules:
            assert module.resource != Resource.Fused

        for tie in self.physical_ties:
            assert tie.src.resource != Resource.Fused, 'src'
            assert tie.dst.resource != Resource.Fused, 'dst'

        for tie in self.ties:
            assert (tie in self.physical_ties) or (tie.src.resource == Resource.Fused) or (tie.dst.resource == Resource.Fused)

        _p_nets = set()
        for module in self.modules:
            if module.resource == Resource.Fused:
                assert module not in self.physical_modules
            else:
                assert module in self.physical_modules, module
                if len(module.outputs) > 0:
                    n = Net()
                    for tie in module.outputs.values():
                        if tie.dst.resource != Resource.Fused:
                            n.add_tie(tie)

                    _p_nets.add(n)

        self._p_nets = frozenset(_p_nets)


    @property
    def modules(self):
        return self._modules


    @property
    def ties(self):
        return self._ties

    @lru_cache(maxsize=32)
    def modules_with_attr(self, attr):
        return frozenset(filter(lambda x : hasattr(x, attr), self.modules))

    @lru_cache(maxsize=32)
    def modules_with_attr_val(self, attr, val):
        return frozenset(filter(lambda x : hasattr(x, attr) and getattr(x, attr) == val, self.modules))

    @property
    def physical_ties(self):
        return self._p_ties

    @property
    def physical_nets(self):
        return self._p_nets

    @property
    def physical_modules(self):
        return self._p_modules
