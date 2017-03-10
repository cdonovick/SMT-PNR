'''
    Classes for represtenting designs and various constructors
'''
from util import NamedIDObject
from types import StringTypes
import Module

class Design(NamedIDObject):
    def __init__(self, adj_dict, op_dict, name=''):
        super().__init__(name)
        self._modules = set()
        self._nets = set()
        self._gen_graph(adj_dict, op_dict)

    @property
    def modules(self):
        return self._modules

    @property
    def nets(self):
        return self._nets
    

    def _gen_graph(self, adj_dict, op_dict):
        mods = dict()
        for src_name, adj_list in self._adj_dict.items():
            if src_name not in mods:
                src = Modules(src_name, op_dict[src_name])
                mods[src_name] = src
                self._modules.add(src)
            else:
                src = mods[src_name]
            
            
            for dst_name, width in adj_list:
                if dst_name not in mods:
                    dst = Modules(dst_name, op_dict[dst_name])
                    mods[dst_name] = dst
                    self._modules.add(dst)
                else:
                    dst = mods[dst_name]

                self._nets.add(Wire(src, dst, width))

