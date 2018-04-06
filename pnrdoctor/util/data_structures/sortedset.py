from collections.abc import MutableSet, Set, Reversible



__all__ = ['SortedSet', 'SortedFrozenSet']


class SortedSet(MutableSet, Reversible):
    __slots__ = '_s', '_l', '_sorted', '_key'

    def __init__(self, it=(), *, key=None):
        self._s = set()
        self._l = list()
        self._key = key

        for i in it:
            self.add(i)


    def __contains__(self, val):
        return val in self._s

    def __iter__(self):
        if not self._sorted:
            self._l.sort(key=self._key)

        yield from self._l

    def __reversed__(self):
        if not self._sorted:
            self._l.sort(key=self._key)

        yield from reversed(self._l)


    def __len__(self):
        return len(self._s)


    def add(self, val):
        if val not in self:
            self._sorted = False
            self._s.add(val)
            self._l.append(val)

    def discard(self, val):
        if val in self:
            self._s.discard(val)
            self._l.remove(val)



class SortedFrozenSet(Set, Reversible):
    __slots__ = '_s', '_l'
    def __init__(self, it=(), *, key=None):
        self._s = set(it)
        self._l = sorted(self._s, key=key)

    def __contains__(self, val):
        return val in self._s

    def __iter__(self):
        yield from self._l

    def __reversed__(self):
        yield from reversed(self._l)

    def __len__(self):
        return len(self._l)
