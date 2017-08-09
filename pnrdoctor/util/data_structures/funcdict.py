from collections.abc import MutableMapping

__all__ = ['FuncDict', 'IdentDict']

class FuncDict(MutableMapping):
    __slots__ = '_d', '_f'
    def __init__(self, f, d=dict()):
        self._d = dict()
        self._f = f
        for k,v in d.items():
            self[k] = v

    def __getitem__(self, key):
        try:
            return self._d[key]
        except KeyError:
            self._d[key] = self._f(key)
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
        s = 'FuncDict({}, {' + ', '.join(c) + '})'.format(self._f)
        return s

def Identity(x): return x

class IdentDict(FuncDict):
    __slots__ = ()
    def __init__(self, d=dict()):
        super().__init__(Identity, d)

    def __repr__(self):
        c = []
        for k,v in self.items():
            c.append('{}:{}'.format(k,v))
        s = 'IdentDict({' + ', '.join(c) + '})'
        return s
