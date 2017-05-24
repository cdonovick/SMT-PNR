from collections import defaultdict, Iterable, OrderedDict, MutableMapping

__all__ = ['BiMultiDict', 'BiDict', 'SortedDict']

class BiMultiDict(MutableMapping):
    def __init__(self, d=dict()):
        self._d = defaultdict(list)
        self._i = defaultdict(list)

        for k,v in d.items():
            if isinstance(v, Iterable) and not isinstance(v, basestring):
                for e in v:
                    self[k] = e
            else:
                self[k] = v

    def __getitem__(self, key):
        return self._d[key]

    def __setitem__(self, key, val):
        self._d[key].append(val)
        self._i[val].append(key)

    def __delitem__(self, key):
        if key not in self._d:
            raise KeyError()

        for val in self._d[key]:
            self._i[val].remove(key)
            if not self._i[val]:
                del self._i[val]

        del self._d[key]
    
    def __contains__(self, key):
        return key in self._d

    def __iter__(self):
        yield from self._d.keys()

    def __repr__(self):
        c = []
        for k,vs in self.items():
            s = '{' + ', '.join(map(str,vs)) + '}'
            c.append('{}:{}'.format(k,s))
        s = '{' + ', '.join(c) + '}'
        return s

    def __len__(self):
        return len(self._d)


    @property
    def I(self):
        t = BiMultiDict()
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

class BiDict(MutableMapping):
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
        s = '{' + ', '.join(c) + '}'
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

class SortedDict(MutableMapping):
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
        s = '{' + ', '.join(c) + '}'
        return s

    def __len__(self):
        return len(self._d)

    def items(self):
        if not self._sorted:
            self._d = OrderedDict(sorted(self._d.items(), key=lambda t: t[0]))
            self._sorted = True

        yield from self._d.items()


