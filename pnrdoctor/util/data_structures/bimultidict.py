from collections import defaultdict
from collections.abc import  MutableMapping, ItemsView, KeysView, ValuesView, Set
from .setlist import SetList

__all__ = ['BiMultiDict']

#view objects for BiMultiDict as the default ones can't handle the the whole multimap thing
class BiMultiDict_keys(KeysView):
    __slots__ = '_d'
    def __init__(self, bmd):
        self._d = bmd._d

    def __contains__(self, elem):
        return elem in self._d

    def __iter__(self):
        yield from self._d

    def __len__(self):
        return len(self._d)

    def __repr__(self):
        c = []
        for v in self:
            c.append('{}'.format(v))

        s = 'BiMultiDict_keys({' + ', '.join(c) + '})'
        return s


class BiMultiDict_items(ItemsView):
    __slots__ = '_d', '_i'
    def __init__(self, bmd):
        self._d = bmd._d
        self._i = bmd._i

    def __contains__(self, elem):
        if isinstance(elem, tuple) and len(elem) == 2:
            return elem[0] in self._d and elem[1] in self._i
        else:
            return False

    def __iter__(self):
        for k in self._d:
            for v in self._d[k]:
                yield (k, v)

    def __len__(self):
        return sum(len(vs) for vs in self._d.values())

    def __repr__(self):
        c = []
        for v in self:
            c.append('{}'.format(v))

        s = 'BiMultiDict_items({' + ', '.join(c) + '})'
        return s

class BiMultiDict_values(ValuesView, Set):
    __slots__ = '_i'
    def __init__(self, bmd):
        self._i = bmd._i

    def __contains__(self, elem):
        return elem in self._i

    def __iter__(self):
        yield from self._i

    def __len__(self):
        return len(self._i)

    def __repr__(self):
        c = []
        for v in self:
            c.append('{}'.format(v))

        s = 'BiMultiDict_values({' + ', '.join(c) + '})'
        return s

class BiMultiDict(MutableMapping):
    __slots__ = '_d', '_i', '_default'
    def __init__(self, d=dict(), default=False):
        '''
          dict    : initial key value pairs
          default :
            BiMultiDict(default=False)[0] -> KeyError()
            BiMultiDict(default=True)[0] -> SetList({})
        '''
        self._d = defaultdict(SetList)
        self._i = defaultdict(SetList)
        self._default = default

        for k,v in d.items():
            self[k] = v

    def __getitem__(self, key):
        if self._default or key in self._d:
            return self._d[key]
        else:
            raise KeyError(key)

    def __setitem__(self, key, val):
        self._d[key].add(val)
        self._i[val].add(key)

    def __delitem__(self, key):
        if key not in self._d:
            raise KeyError(key)

        for val in self._d[key]:
            self._i[val].remove(key)
            if not self._i[val]:
                del self._i[val]

        del self._d[key]

    def del_kvpair(self, key, val):
        if key not in self._d:
            raise KeyError(key)

        for v in self._d[key]:
            if v == val:
                self._d[key].remove(val)
                self._i[v].remove(key)                
                if not self._i[val]:
                    del self._i[val]
                if not self._d[key]:
                    del self._d[key]
                break


    def __contains__(self, key):
        return key in self._d

    def __iter__(self):
        yield from self._d.keys()

    def __repr__(self):
        c = []
        for k in self:
            vs = self[k]
            s = '{' + ', '.join(map(str,vs)) + '}'
            c.append('{}:{}'.format(k,s))

        s = 'BiMultiDict({' + ', '.join(c) + '}}, default={})'.format(self._default)
        return s

    def __len__(self):
        return len(self._d)

    def keys(self):
        return BiMultiDict_keys(self)

    def items(self):
        '''
           Returns flat version of key, value pairs
        '''
        return BiMultiDict_items(self)

    def values(self):
        '''
           Returns all the values as a flat set
        '''
        return BiMultiDict_values(self)

    @property
    def I(self):
        t = BiMultiDict(default=self._default)
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
