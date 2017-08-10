'''
    Classes for represtenting designs and various constructors
'''
from collections import defaultdict
from pnrdoctor.util import NamedIDObject, SortedDict
from .module import Module, Resource
from .net import Net, Tie
from functools import lru_cache


class Design(NamedIDObject):
    def __init__(self, modules, ties, name=''):
        super().__init__(name)

        ################## netlist modification passes #############

        # comments are of the form
        # (modules | ties): input representation --> output representation

        # HACK to make only one wire leave input
        # modules: dict representation --> dict representation
        # ties: tuple representation --> tuple representation
        modules, ties = _io_hack(modules, ties)

        # modules: dict representation --> {mod_name: Module}
        # ties: unchanged
        modules, ties = _build_modules(modules, ties)

        # modules: unchanged
        # ties: tuple representation --> {tuple: Tie}
        modules, ties = _build_ties(modules, ties)

        self._modules=frozenset(modules.values())
        self._ties=frozenset(ties.values())

        # produce physical modules and physical ties
        # modules: {mod_name: Module} --> set of physical modules
        # ties: {tuple: Tie} --> set of physical ties
        p_modules, p_ties = _fuse_comps(modules, ties)

        self._p_modules = frozenset(p_modules)
        self._p_ties = frozenset(p_ties)

        # assertions
        for module in self.modules:
            assert module.resource != Resource.UNSET

        for module in self.physical_modules:
            assert module.resource != Resource.Fused

        for tie in self.physical_ties:
            assert tie.src.resource != Resource.Fused, 'src'
            assert tie.dst.resource != Resource.Fused, 'dst'

        for tie in self.ties:
            assert (tie in self.physical_ties) or \
              (tie.src.resource == Resource.Fused) or \
              (tie.dst.resource == Resource.Fused)

        # end assertions

        # if it ever becomes useful, can fuse the rest of the
        # registers and build nets -- functions are in design/passes.py
        # rf_modules, rf_ties = collapse_all_regs(mods, ties, self._p_ties)
        # _rf_nets = build_nets(self._rf_modules)
        # self._rf_nets = frozenset(_rf_nets)


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
    def physical_modules(self):
        return self._p_modules


def _io_hack(mods, ties):
    # to help CGRA team with io hack
    # creating a dummy PE (i.e. input + 0)

    # find input modules
    inputmods = defaultdict(int)
    for src_name, src_port, dst_name, dst_port, width in ties:
        if mods[src_name]['type'] == 'IO':
            #an output should never be a src
            assert mods[src_name]['conf'] == 'i'
            inputmods[src_name] += 1

    #filter the inputs for inputs with more than one input
    inputmods = {k for k,v in inputmods.items() if v > 1}

    #we need to hack some inputs
    if inputmods:
        #create const_0 module
        const_0_name = '__HACK__io_const_0'
        assert const_0_name  not in mods, 'Hack name ({}) in use things are going to break'.format(const_0_name)
        mods[const_0_name] = {
                'type' : 'Const',
                'conf' : 0,
                'res'  : Resource.UNSET,
            }

        #change all the mods to be adders
        for mod_name in inputmods:
            saved_args = mods[mod_name].copy()
            mods[mod_name]['type'] = 'PE'
            mods[mod_name]['conf'] = 'add'
            mods[mod_name]['res']  = Resource.PE

            hack_io_name = '__HACK__' + mod_name
            assert hack_io_name not in mods, 'Hack name ({}) in use things are going to break'.format(hack_io_name)

            #make a hack mod
            mods[hack_io_name] = saved_args

            # make a tie from the hack mod to original io (the now adder)
            # assuming 16 width but we are fucked if its not anyway as the adder trick wont work
            ties.add((hack_io_name, 'pe_out_res', mod_name, 'a', 16))
            # make a tie from the const 0 to original io (the now adder)
            ties.add((const_0_name, 'out', mod_name, 'b', 16))
    return mods, ties


def _build_modules(mods, ties):
    _mods = SortedDict()

    for mod_name, args in mods.items():
        mod = Module(mod_name)
        mod.type_ = args['type']
        if args['conf'] is not None:
            mod.config = args['conf']

        mod.resource = args['res']
        _mods[mod_name] = mod

    return _mods, ties


def _build_ties(mods, ties):

    # fusable combination of resource types
    _fusable = {(s, d) for s in ('Reg', 'Const') for d in ('PE',)}

    fuse_me = set()
    fuse_no = set()

    _ties = dict()
    for src_name, src_port, dst_name, dst_port, width in ties:

        src = mods[src_name]
        dst = mods[dst_name]
        idx = (src, src_port, dst, dst_port, width)

        if (src.type_, dst.type_) in _fusable:
            fuse_me.add(src)
        else:
            fuse_no.add(src)

        _ties[idx] = Tie(*idx)

    # mark fused mods
    for m in mods.values():
        if m not in fuse_no and m in fuse_me:
            m.resource = Resource.Fused

    return mods, _ties


def _fuse_comps(mods, ties):

    _new_ties = set()

    for mod in mods.values():
        if mod.resource == Resource.Fused:
            for tie in mod.outputs.values():
                if mod.type_ == 'Reg':
                    new_tie = tie.dst.collapse_input(tie.dst_port)
                    _new_ties.add(new_tie)
                # if it's a Const, it will be fused but the tie will
                # still be an input -- nothing needs to be done

    _p_ties = set([tie for tie in _new_ties.union(ties.values()) \
                if tie.src.resource != Resource.Fused and \
                tie.dst.resource != Resource.Fused])

    _p_modules = [mod for mod in mods.values() if mod.resource != Resource.Fused]

    return _p_modules, _p_ties


def _collapse_all_regs(mods, ties, p_ties):
    _new_ties = set()
    for mod in mods.values():
        if mod.resource == Resource.Reg:
            for tie in mod.outputs.values():
                    new_tie = tie.dst.collapse_input(tie.dst_port)
                    _new_ties.add(new_tie)

    # remove register ties
    _rf_ties = set([tie for tie in _new_ties.union(p_ties) \
                    if tie.src.resource != Resource.Reg and \
                    tie.dst.resource != Resource.Reg])

    _rf_modules = set()
    for rf_tie in _rf_ties:
        _rf_modules.add(rf_tie.src)
        _rf_modules.add(rf_tie.dst)

    return _rf_modules, _rf_ties


def _build_nets(rf_mods):
    '''
       Takes in modules and returns regfree nets
       Nets are a collection of ties that share a source
    '''
    _p_nets = set()

    for mod in rf_mods:
        if len(mod.outputs) > 0:
            n = Net()
            for tie in mod.outputs.values():
                n.add_tie(tie)

            _p_nets.add(n)

    return _p_nets
