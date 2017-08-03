'''
   Passes for transforming the design
'''
from util import SortedDict
from .module import Module, Resource
from .net import Tie, Net
from collections import defaultdict

_fusable = {(s, d) for s in ('Reg', 'Const') for d in ('PE',)}


def io_hack(mods, ties):
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

                #make a tie from the hack mod to original io (the now adder)
                #assuming 16 width but we are fucked if its not anyway as the adder trick wont work
                ties.add((hack_io_name, 'pe_out_res', mod_name, 'a', 16))
                #make a tie from the const 0 to original io (the now adder)
                ties.add((const_0_name, 'out', mod_name, 'b', 16))



def build_modules(mods):
    _mods = SortedDict()
    
    for mod_name, args in mods.items():
        mod = Module(mod_name)
        mod.type_ = args['type']
        if args['conf'] is not None:
            mod.config = args['conf']

        mod.resource = args['res']
        _mods[mod_name] = mod

    return _mods


def build_ties(mods, ties):

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

    return _ties


def fuse_regs(mods, ties):

    def _input_collapse_pass(_new_ties, mods, resource):
        for mod in mods:
            if mod.resource == resource:
                for tie in mod.outputs.values():
                    if mod.type_ == 'Reg':
                        new_tie = tie.dst.collapse_input(tie.dst_port)
                        _new_ties.add(new_tie)
                    # if it's a Const, it will be fused but the tie will
                    # still be an input -- nothing needs to be done
    _new_ties = set()

    _input_collapse_pass(_new_ties, mods.values(), Resource.Fused)

    _p_ties = set([tie for tie in _new_ties.union(ties.values()) \
                if tie.src.resource != Resource.Fused and \
                tie.dst.resource != Resource.Fused])

    nonfused_mods = [mod for mod in mods.values() if mod.resource != Resource.Fused]
    _input_collapse_pass(_new_ties, nonfused_mods, Resource.Reg)

    # remove register ties
    _rf_ties = set([tie for tie in _new_ties.union(_p_ties) \
                    if tie.src.resource != Resource.Reg and \
                    tie.dst.resource != Resource.Reg])

    _p_modules = set()
    _rf_modules = set()
    for p_tie in _p_ties:
        _p_modules.add(p_tie.src)
        _p_modules.add(p_tie.dst)

        if p_tie.src.resource != Resource.Reg:
            _rf_modules.add(p_tie.src)

        if p_tie.dst.resource != Resource.Reg:
            _rf_modules.add(p_tie.dst)
    
    return _p_modules, _rf_modules, _p_ties, _rf_ties


def build_nets(rf_mods):
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
