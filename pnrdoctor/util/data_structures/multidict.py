from collections import defaultdict
from collections.abc import  MutableMapping, ItemsView, KeysView, ValuesView, Set
from .setlist import SetList

__all__ = ['MultiDict']

#view objects for BiMultiDict as the default ones can't handle the the whole multimap thing
class MultiDict_keys(KeysView):
    __slots__ = '_view'
    def __init__(self, md):
        self._view = md._d.keys()

    def __contains__(self, elem):
        return elem in self._view

    def __iter__(self):
        yield from self._view

    def __len__(self):
        return len(self._view)

    def __repr__(self):
        c = []
        for v in self:
            c.append('{}'.format(v))

        s = 'MultiDict_keys({' + ', '.join(c) + '})'
        return s


class MultiDict_items(ItemsView):
    __slots__ = '_d'
    def __init__(self, md):
        self._d = md._d

    def __contains__(self, elem):
        if isinstance(elem, tuple) and len(elem) == 2:
            return elem[0] in self._d and elem[1] in self._d[elem[0]]
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

        s = 'MultiDict_items({' + ', '.join(c) + '})'
        return s


class MultiDict_values(ValuesView, Set):
    __slots__ = '_view'
    def __init__(self, md):
        self._view = md._d.values()

    def __contains__(self, elem):
        return any(elem in vs for vs in self._view)

    def __iter__(self):
        s = set()
        for vs in self._view:
            for v in vs:
                if v not in s:
                    yield v
                    s.add(v)

    def __len__(self):
        return sum(len(vs) for vs in self._view)

    def __repr__(self):
        c = []
        for v in self:
            c.append('{}'.format(v))

        s = 'MultiDict_values({' + ', '.join(c) + '})'
        return s


class MultiDict(MutableMapping):
    __slots__ = '_d', '_default'
    def __init__(self, d=dict(), default=False):
        '''
          dict    : initial key value pairs
          default :
            MultiDict(default=False)[0] -> KeyError()
            MultiDict(default=True)[0] -> SetList({})
        '''
        self._d = defaultdict(SetList)
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

    def __delitem__(self, key):
        del self._d[key]

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

        s = 'MultiDict({' + ', '.join(c) + '}, default=' + str(self._default) + ')'
        return s

    def __len__(self):
        return len(self._d)

    def keys(self):
        return MultiDict_keys(self)

    def items(self):
        '''
           Returns flat version of key, value pairs
        '''
        return MultiDict_items(self)

    def values(self):
        '''
           Returns all the values as a flat set
        '''
        return MultiDict_values(self)
