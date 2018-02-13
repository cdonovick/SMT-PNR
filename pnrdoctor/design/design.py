'''
    Classes for represtenting designs and various constructors
'''
from collections import defaultdict
from pnrdoctor.util import NamedIDObject, SortedDict, MultiDict
from .module import Module, Resource, Layer
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
        # modules, ties = _io_hack(modules, ties)

        modules, ties = _split_registers(modules, ties)

        # modules: dict representation --> {mod_name: Module}
        # ties: unchanged
        modules, ties = _build_modules(modules, ties)

        # modules: unchanged
        # ties: tuple representation --> {tuple: Tie}
        modules, ties = _build_ties(modules, ties)

        # modules: {mod_name: Module} --> set of final modules
        # ties: {tuple: Tie} --> set of final ties
        modules, ties = _fuse_regs(modules, ties)

        self._modules = frozenset(modules)
        self._ties = frozenset(ties)

        layers = set()
        for tie in ties:
            layers.add(tie.width)

        self._layers = frozenset(layers)


        nets = MultiDict()
        for tie in ties:
            nets[(tie.src, tie.src_port, tie.width)] = tie

        _nets = set()
        for n in nets:
            _nets.add(Net(nets[n]))

        self._nets = frozenset(_nets)

        # assertions
        for module in self.modules:
            assert module.resource != Resource.UNSET, module
            assert module.layer != Layer.UNSET, module

        for tie in self.ties:
            assert tie in tie.dst.inputs.values(), tie
            assert tie in tie.src.outputs.values(), tie

        for module in self.modules:
            for tie in module.inputs.values():
                assert module is tie.dst
            for tie in module.outputs.values():
                assert module is tie.src
        # end assertions

    @property
    def modules(self):
        return self._modules

    @property
    def ties(self):
        return self._ties

    @property
    def nets(self):
        return self._nets

    @property
    def layers(self):
        return self._layers

    @lru_cache(maxsize=32)
    def modules_with_attr(self, attr):
        return frozenset(filter(lambda x : hasattr(x, attr), self.modules))

    @lru_cache(maxsize=32)
    def modules_with_attr_val(self, attr, val):
        return frozenset(filter(lambda x : hasattr(x, attr) and getattr(x, attr) == val, self.modules))


def _io_hack(mods, ties):
    # to help CGRA team with io hack
    # creating a dummy PE (i.e. input + 0)

    # find input modules
    inputmods = defaultdict(int)
    for src_name, src_port, dst_name, dst_port, width in ties:
        if mods[src_name]['type'] == 'IO':
            #an output should never be a src
            assert mods[src_name]['conf'] == 'i', (mods[src_name], mods[src_name]['conf'])
            inputmods[src_name] += 1

    #filter the inputs for inputs with more than one input
    inputmods = {k for k,v in inputmods.items() if v > 1}

    #we need to hack some inputs
    if inputmods:
        #create const_0 module
        const_0_name = '__HACK__io_const_0'
        assert const_0_name  not in mods, 'Hack name ({}) in use things are going to break'.format(const_0_name)
        mods[const_0_name] = {
                'type'  : 'Const',
                'res'   : Resource.Fused,  # always fuse constants
                'layer' : Layer.Data,
                'conf'  : 0,
            }

        #change all the mods to be adders
        for mod_name in inputmods:
            saved_args = mods[mod_name].copy()
            mods[mod_name]['type'] = 'PE'
            mods[mod_name]['conf'] = {'alu_op' : 'add'}
            mods[mod_name]['res']  = Resource.PE

            hack_io_name = '__HACK__' + mod_name
            assert hack_io_name not in mods, 'Hack name ({}) in use things are going to break'.format(hack_io_name)

            #make a hack mod
            mods[hack_io_name] = saved_args

            # make a tie from the hack mod to original io (the now adder)
            # assuming 16 width but we are fucked if its not anyway as the adder trick wont work
            ties.add((hack_io_name, 'pe_out_res', mod_name, 'data0', Layer.Data.width))
            # make a tie from the const 0 to original io (the now adder)
            ties.add((const_0_name, 'out', mod_name, 'data1', Layer.Data.width))
    return mods, ties

def _split_registers(mods, ties):
    fusable = MultiDict()
    fuse_names = MultiDict()
    has_register_out = set()
    m_delete = set()
    t_delete = set()

    for tie in ties:
        src_name, _, dst_name, _, _ = tie
        if mods[src_name]['type'] == 'Reg':
            if mods[dst_name]['type'] == 'PE':
                fusable[src_name] = tie
            elif mods[dst_name]['type'] == 'Reg':
                has_register_out.add(src_name)

    for r_name in fusable:
        for k,tie in enumerate(fusable[r_name]):
            src_name, src_port, dst_name, dst_port, width = tie
            assert src_name == r_name, "Something is broken with my logic"

            f_name = '__FUSED__{}_{}'.format(k, r_name)
            assert f_name not in mods, 'Fused name ({}) in use things are going to break'.format(f_name)
            fuse_names[r_name] = f_name

            # add new register
            mods[f_name] = dict()
            mods[f_name]['type'] = 'Reg'
            mods[f_name]['res']  = Resource.Fused  # mark the new register as fused
            mods[f_name]['layer'] = mods[r_name]['layer']
            mods[f_name]['conf'] = None

            # add new tie
            ties.add((f_name, src_port, dst_name, dst_port, width))

            # mark old tie for deletion
            t_delete.add(tie)

        if r_name not in has_register_out:
            #mark old register for deletion
            m_delete.add(r_name)

    ties2add = set()

    for tie in ties:
        src_name, src_port, dst_name, dst_port, width = tie
        #find all ties with a fused register as dst and create new tie
        if dst_name in fusable:
            assert dst_name in fuse_names
            for f_name in fuse_names[dst_name]:
                ties2add.add((src_name, src_port, f_name, dst_port, width))

        #if dst is marked for deletation delete tie
        if dst_name in m_delete:
            t_delete.add(tie)

    ties = ties.union(ties2add)

    for mod in m_delete:
        del mods[mod]

    for tie in t_delete:
        ties.remove(tie)

    return mods, ties


def _build_modules(mods, ties):
    _mods = SortedDict()

    for mod_name, args in mods.items():
        mod = Module(mod_name)
        mod.type_ = args['type']
        if args['conf'] is not None:
            mod.config = args['conf']

        mod.resource = args['res']
        mod.layer = args['layer']
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


def _fuse_regs(mods, ties):
    # fuse all Register to PE connections
    for m in mods.values():
        if m.resource == Resource.Fused and 'Reg' in m.type_:
            assert len(m.outputs) == 1, 'Fused regs should have one output'
            output_tie = next(iter(m.outputs.values()))
            assert output_tie.dst.resource == Resource.PE, 'Fused register should have one PE output'
            assert len(m.inputs) == 1, 'Fused register should have only one input'
            input_tie = next(iter(m.inputs.values()))
            assert input_tie.width == output_tie.width

            # delete dict pointers to old ties
            del output_tie.dst.inputs[output_tie.dst_port]
            # delete only one of the outputs!
            input_tie.src.outputs.del_kvpair(input_tie.src_port, input_tie)

            # create new tie
            new_tie = Tie(input_tie.src, input_tie.src_port, output_tie.dst, output_tie.dst_port, output_tie.width)
            # mark the port as registered
            output_tie.dst.add_registered_input(output_tie.dst_port)

    _p_modules = set([mod for mod in mods.values() if mod.resource != Resource.Fused])

    _p_ties = set()
    for m in _p_modules:
        for tie in m.inputs.values():
            if tie.src.resource != Resource.Fused:
                _p_ties.add(tie)
        for tie in m.outputs.values():
            assert tie.dst.resource != Resource.Fused, \
              'There should not be leftover ties pointing to fused modules'
            _p_ties.add(tie)

    return _p_modules, _p_ties
