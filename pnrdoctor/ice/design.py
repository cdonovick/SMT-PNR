class IceDesign(NamedIDObject):
    def __init__(self, modules, ties, name=''):
        super().__init__(name)

    @property
    def modules(self):
        return self._modules

    @property
    def ties(self):
        return self._ties



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
