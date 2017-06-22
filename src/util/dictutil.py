from collections import defaultdict, Iterable, OrderedDict, MutableMapping, MutableSet, Sequence

__all__ = ['BiMultiDict', 'BiDict', 'SortedDict', 'IdentDict', 'SetList']

class SetList(MutableSet, Sequence):
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

    def __getitem__(self, key):
        return self._l[key]

    def __repr__(self):
        c = []
        for v in self:
            c.append('{}'.format(v))

        s = 'SetList({' + ', '.join(c) + '})'
        return s

class BiMultiDict(MutableMapping):
    def __init__(self, d=dict()):
        self._d = defaultdict(SetList)
        self._i = defaultdict(SetList)

        for k,v in d.items():
            if isinstance(v, Iterable) and not isinstance(v, basestring):
                for e in v:
                    self[k] = e
            else:
                self[k] = v

    def __getitem__(self, key):
        return self._d[key]

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

    def __contains__(self, key):
        return key in self._d

    def __iter__(self):
        yield from self._d.keys()

    def __repr__(self):
        c = []
        for k,vs in self.items():
            s = '{' + ', '.join(map(str,vs)) + '}'
            c.append('{}:{}'.format(k,s))
        s = 'BiMultiDict({' + ', '.join(c) + '})'
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
        s = 'SortedDict({' + ', '.join(c) + '})'
        return s

    def __len__(self):
        return len(self._d)

    def items(self):
        if not self._sorted:
            self._d = OrderedDict(sorted(self._d.items(), key=lambda t: t[0]))
            self._sorted = True

        yield from self._d.items()

class IdentDict(MutableMapping):
    def __init__(self, d=dict()):
        self._d = dict()
        for k,v in d.items():
            self[k] = v

    def __getitem__(self, key):
        try:
            return self._d[key]
        except KeyError:
            self._d[key] = key
            return  self._d[key]

    def __setitem__(self, key, val):
        self._d[key] = val

    def __delitem__(self, key):
        del self._d[key]

    def __iter__(self):
        yield from self._d.keys()

    def __len__(self):
        return len(self._d)

    def __contains__(self, key):
        return key in self._d

    def __repr__(self):
        c = []
        for k,v in self.items():
            c.append('{}:{}'.format(k,v))
        s = 'IdentDict({' + ', '.join(c) + '})'
        return s
