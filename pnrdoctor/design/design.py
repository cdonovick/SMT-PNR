'''
    Classes for represtenting designs and various constructors
'''
from collections import defaultdict
from util import NamedIDObject
from .module import Resource
from .net import Net
from .passes import io_hack, build_modules, build_ties, fuse_regs, build_nets
from functools import lru_cache

class Design(NamedIDObject):
    def __init__(self, modules, ties, name=''):
        super().__init__(name)

        # HACK to make only one wire leave input
        # to help CGRA team with io hack
        # creating a dummy PE (i.e. input + 0)
        io_hack(modules, ties)  # this function modifies modules and ties

        _mods = build_modules(modules)
        _ties = build_ties(_mods, ties)
        self._modules=frozenset(_mods.values())
        # TODO: Decide if we want ties to be pre or post processing
        self._ties=frozenset(_ties.values())

        _p_modules, _p_ties = fuse_regs(_mods, _ties)
        self._p_modules = frozenset(_p_modules)
        self._p_ties = frozenset(_p_ties)

        # assertions

        for module in self.modules:
            assert module.resource != Resource.UNSET

        for module in self.physical_modules:
            assert module.resource != Resource.Fused

        for tie in self.physical_ties:
            assert tie.src.resource != Resource.Fused, 'src'
            assert tie.dst.resource != Resource.Fused, 'dst'

        _fusable_resources = {Resource.Reg, Resource.Fused}
        for tie in self.ties:
            assert (tie in self.physical_ties) or \
              (tie.src.resource in _fusable_resources) or \
              (tie.dst.resource in _fusable_resources)

        # end assertions

        # currently only building physical_nets
        _p_nets = build_nets(self._p_modules)
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
