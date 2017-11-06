from pnrdoctor.util import IDObject, NamedIDObject

from collections import namedtuple

Connection = namedtuple('Connection', ['module', 'port'])

class Net(NamedIDObject):
    '''
       Holds a collection of ties that make up a net.
    '''
    def __init__(self, name, src, dsts):
        super().__init__(name)
        dsts = {c for c in dsts}
        self._dsts = frozenset(dsts)
        self._src  = src
        self._degree = len(dsts) + 1
    
    @property
    def degree(self):
        return self._degree

    @property
    def connections(self):
        yield self._src
        yield from self._dsts

    @property
    def modules(self):
        yield from map(lambda c : c.module, self.connections)

    @property
    def dsts(self):
        return self._dsts

    @property
    def src(self):
        return self._src

    @property
    def ties(self):
        src = self.src
        for dst in self.dsts:
            yield (src, dst) 
