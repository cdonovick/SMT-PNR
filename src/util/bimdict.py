from collections import defaultdict, Iterable

class BiMultiDict:
    def __init__(self, d=dict()):
        self._d = defaultdict(set)
        self._i = defaultdict(set)

        for k,v in d.items():
            if isinstance(v, Iterable) and not isinstance(v, basestring):
                for e in v:
                    self[k] = e
            else:
                self[k] = v

    def __getitem__(self, key):
        return self._d(key)

    def __setitem__(self, key, val):
        self._d[key].add(val)
        self._i[val].add(key)

    def __delitem__(self, key):
        if key not in self._d:
            raise KeyError()

        for val in self._d[key]:
            self._i[val].remove(key)
            if not self._i[val]:
                del self._i[val]

        del self._d[key]

    def __iter__(self):
        return iter(self.keys())

    def __repr__(self):
        c = []
        for k,vs in self.items():
            s = '{' + ', '.join(map(str,vs)) + '}'
            c.append('{}:{}'.format(k,s))
        s = '{' + ', '.join(c) + '}'
        return s

    def __len__(self):
        return len(self._d)

    def keys(self):
        for k in self._d.keys():
            yield k

    def items(self):
        for k,v in self._d.items():
            yield (k,v)

    def values(self):
        for v in self._d.values():
            yield v

    @property
    def I(self):
        return _View(self)

    def _attest(self):
        for k,vs in self._d.items():
            for v in vs: 
                assert k in self._i[v]

        for k,vs in self._i.items():
            for v in vs:
                assert k in self._d[v]

class _View(BiMultiDict):
    def __init__(self, orig):
        self._d = orig._i
        self._i = orig._d

