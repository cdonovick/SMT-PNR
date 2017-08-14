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

        self._modules=frozenset(modules.values())

        # modules: unchanged
        # ties: tuple representation --> {tuple: Tie}
        modules, ties = _build_ties(modules, ties)

        # produce physical modules and modify ties
        # modules: {mod_name: Module} --> set of physical modules
        # ties: {tuple: Tie} --> set of physical ties
        p_modules, p_ties = _fuse_comps(modules, ties)

        self._p_modules = frozenset(p_modules)
        self._ties = frozenset(p_ties)

        # assertions
        for module in self.modules:
            assert module.resource != Resource.UNSET

        for module in self.physical_modules:
            assert module.resource != Resource.Fused

        for tie in self.ties:
            assert (tie in self.ties) or \
              (tie.src.resource in {Resource.Reg, Resource.Fused}) or \
              (tie.dst.resource in {Resource.Reg, Resource.Fused}), tie

        for tie in self.ties:
            assert tie in tie.dst.inputs.values(), tie

        # end assertions

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

    _ties = dict()
    for src_name, src_port, dst_name, dst_port, width in ties:

        src = mods[src_name]
        dst = mods[dst_name]
        idx = (src, src_port, dst, dst_port, width)

        _ties[idx] = Tie(*idx)

    return mods, _ties


def _fuse_comps(mods, ties):
    '''
       Inputs
       mods: {module_name: Module}
       ties: {tie_index_tuple: Tie}

       Fuses all constants
       Fuses registers -- preference is to put as many registers as possible in PEs
       For more detailed documentation see the comments at the top of the function
    '''

    # This function fuses Const and Reg components
    # Consts are all assigned Resource.Fused, but no new ties need to be created, because Consts
    #    are always sources with no inputs.
    # Regs are assigned Resource.Fused if all of their outputs are PEs or IO
    # However, Regs that are not "fully fused" can still be fused on some ties
    # Example:
    #      m1 --> r1 --> r2 --> m3
    #             |
    #             --> m2
    # r2 can be completely fused into m3's input
    # However, r1 cannot be fused because there is only one available register on a PE's input port,
    # but m1 and m3 must be connected by two registers
    #
    # That being said, r1 could be fused into m2
    #
    # Therefore, we fuse r1 into m2, but leave it there for the r2 connection.
    # This corresponds to modifying the ties
    #
    # The set of ties becomes (fr denotes a tie with a fused register on it):
    # m1 --> r1
    # r1 --> m3 fr
    # m1 --> m2 fr

    for m in mods.values():
        if m.type_ == 'Const':
            m.resource = Resource.Fused
        elif m.resource == Resource.Reg:
            if all([om.dst.resource != Resource.Reg for om in m.outputs.values()]):
                m.resource = Resource.Fused

    _new_ties = set()
    _ties2remove = set()

    for mod in mods.values():
        if mod.resource in {Resource.Fused, Resource.Reg} and mod.type_ == "Reg":
            for tie in mod.outputs.values():
                if not tie.fused_reg and tie.dst.resource not in {Resource.Reg, Resource.Fused}:
                    new_tie = tie.dst.fuse_reg(tie.dst_port)
                    _new_ties.add(new_tie)
                    _ties2remove.add(tie)
        # if it's a Const, it will be fused but the tie will
        # still be an input -- nothing needs to be done

    _p_ties = set([tie for tie in _new_ties.union(ties.values()) \
                if tie.src.resource != Resource.Fused and \
                tie.dst.resource != Resource.Fused]) - _ties2remove

    _p_modules = [mod for mod in mods.values() if mod.resource != Resource.Fused]

    return _p_modules, _p_ties
