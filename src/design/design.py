'''
    Classes for represtenting designs and various constructors
'''
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
        hackidx = 0
        newmodules = {}
        input2adders = {}
        input2consts = {}
        for mod_name, args in modules.items():
            if args['type'] == 'IO' and args['conf'] == 'i':
                addname = 'iohackadder{}'.format(hackidx)
                constname = 'iohackconst{}'.format(hackidx)
                newadderargs = {'res': Resource.PE, 'type': 'PE', 'conf': 'add'}
                newadder = {addname: newadderargs}
                newconstargs = {'res': Resource.UNSET, 'type': 'Const', 'conf': 0}
                newconst = {constname: newconstargs}
                newmodules.update(newadder)
                newmodules.update(newconst)
                input2adders[mod_name] = addname
                input2consts[mod_name] = constname
                hackidx += 1

        # add the new hack modules to modules
        modules.update(newmodules)

        newnets = set()
        toremove = set()
        # replace input with dummy adder
        for src_name, src_port, dst_name, dst_port, width in nets:
            if src_name in input2adders:
                toremove.add((src_name, src_port, dst_name, dst_port, width))
                newnets.add((input2adders[src_name], src_port, dst_name, dst_port, width))

        # remove the input elements
        nets = nets - toremove

        # replace with dummy adder
        nets = nets.union(newnets)

        # make const 0 --> dummyadder connection
        for io, const in input2consts.items():
            nets.add((const, 'out', input2adders[io], 'b', 16))

        # connect the input to the dummy adder
        for io, adder in input2adders.items():
            nets.add((io, 'pe_out_res', adder, 'a', 16))

        # end HACK for IOs


        #build modules
        for mod_name,args in modules.items():
            mod = Module(mod_name)
            mod.type_ = args['type']
            mod.fused = False
            if args['conf'] is not None:
                mod.config = args['conf']

            mod.resource = args['res']
            _mods[mod_name] = mod

        self._modules=frozenset(_mods.values())

        fuse_me = set()
        fuse_no = set()

        #build nets
        idx_set = set()
        for src_name, src_port, dst_name, dst_port, width in nets:

            src = _mods[src_name]
            dst = _mods[dst_name]
            idx = (src, src_port, dst, dst_port, width)

            if (src.type_, dst.type_) in _fusable:
                fuse_me.add(src)
            else:
                fuse_no.add(src)
                #for virtual nets
                idx_set.add(idx)


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

        #build _p_nets
        _p_nets = set()
        while idx_set:
            idx = idx_set.pop()
            #idx[2] == dst
            if idx[2].resource != Resource.Fused:
                if idx in _nets:
                    _p_nets.add(_nets[idx])
                else:
                    t = Net(*idx)
                    _p_nets.add(t)
            else:
                for dst_net in idx[2].outputs.values():
                    assert dst_net.width == idx[4]
                    #print("Fusing: \n({a}  ->  {b})\n ({b}  ->  {c})\n({a}  ->  {c})\n".format(a=idx[0].name, b=idx[2].name, c=dst_net.dst.name))
                    idx_set.add((idx[0], idx[1], dst_net.dst, dst_net.dst_port, idx[4]))

        self._p_nets = frozenset(_p_nets)

        for module in self.modules:
            assert module.resource != Resource.UNSET

        for module in self.physical_modules:
            assert module.resource != Resource.Fused

        for net in self.physical_nets:
            assert net.src.resource != Resource.Fused, 'src'
            assert net.dst.resource != Resource.Fused, 'dst'

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
