from collections.abc import MutableMapping

__all__ = ['BiDict']

class BiDict(MutableMapping):
    __slots__ = '_d', '_i'
    def __init__(self, d=dict()):
        self._d = dict()
        self._i = dict()

        for k,v in d.items():
            self[k] = v

    def __getitem__(self, key):
        return self._d[key]

    def __setitem__(self, key, val):
        self._d[key] = val
        self._i[val] = key

    def __delitem__(self, key):
        if key not in self._d:
            raise KeyError()

        val = self._d[key]
        del self._i[val]
        del self._d[key]

    def __iter__(self):
        yield from self._d.keys()

    def __repr__(self):
        c = []
        for k,v in self.items():
            c.append('{}:{}'.format(k,v))
        s = 'BiDict({' + ', '.join(c) + '})'
        return s

    def __len__(self):
        return len(self._d)

    @property
    def I(self):
        t = BiDict()
        t._d = self._i
        t._i = self._d
        return t

    def _attest(self):
        for k,vs in self._d.items():
            for v in vs:
                assert k in self._i[v]

        for k,vs in self._i.items():
            for v in vs:
                assert k in self._d[v]
