from collections import OrderedDict
from collections.abc import MutableMapping

__all__ = ['SortedDict']

class SortedDict(MutableMapping):
    __slots__ = '_d', '_sorted'
    def __init__(self, d=dict()):
        self._d = OrderedDict()
        self._sorted = True
        for k,v in d.items():
            self[k] = v

    def __getitem__(self, key):
        return self._d[key]

    def __setitem__(self, key, val):
        self._sorted = False
        self._d[key] = val

    def __delitem__(self, key):
        del self._d[key]

    def __iter__(self):
        for k, _ in self.items():
            yield k

    def __repr__(self):
        c = []
        for k,v in self.items():
            c.append('{}:{}'.format(k,v))
        s = 'SortedDict({' + ', '.join(c) + '})'
        return s

    def __len__(self):
        return len(self._d)

    def items(self):
        if not self._sorted:
            self._d = OrderedDict(sorted(self._d.items(), key=lambda t: t[0]))
            self._sorted = True

        yield from self._d.items()
