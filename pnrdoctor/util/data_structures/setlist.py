from collections.abc import MutableSet, Sequence

__all__ = ['SetList']

class SetList(MutableSet, Sequence):
    __slots__ = '_s', '_l'

    def __init__(self, iter=()):
        self._s = set()
        self._l = list()

        for i in iter:
            self.add(i)

    def __contains__(self, val):
        return val in self._s

    def __iter__(self):
        yield from self._l

    def __len__(self):
        return len(self._s)

    def add(self, val):
        if val not in self:
            self._s.add(val)
            self._l.append(val)

    def discard(self, val):
        if val in self:
            self._s.discard(val)
            self._l.remove(val)

    def pop(self):
        val = self._l.pop()
        self._s.remove(val)
        return val

    def __getitem__(self, key):
        return self._l[key]

    def __repr__(self):
        c = []
        for v in self:
            c.append('{}'.format(v))

        s = 'SetList({' + ', '.join(c) + '})'
        return s
