from collections.abc import MutableMapping, Set
from .setlist import SetList
from util import class_property, Constant

__all__ = ['SelectDict', 'STAR']


class _STAR(Constant):
    __slots__ = ()

    def __eq__(self, other):
        return True


STAR = _STAR()


class SelectDict_matching_keys(Set):
    __slots__ = '_view', '_pattern'

    def __init__(self, sd, pattern):
        self._view = sd._d.keys()
        self._pattern = pattern

    def __contains__(self, elem):
        return elem == self._pattern and elem in self._view

    def __iter__(self):
        yield from filter(lambda e : e == self._pattern, self._view)

    def __len__(self):
        return len(list(self))

    def __repr__(self):
        c = []
        for k in self:
            c.append('{}'.format(k))

        s = 'SelectDict_matching_keys({' + ', '.join(c) + '})'
        return s


class SelectDict(MutableMapping):
    _STAR = _STAR()
    __slots__ = '_d'

    def __init__(self, d=dict()):
        self._d = dict()

        for k,v in d.items():
            self[k] = v

    @classmethod
    def _checkstar(cls, key):
        return any(v is cls.STAR for v in key)

    def __getitem__(self, key):
        if not self._checkstar(key):
            return self._d[key]
        else:
            return SetList(self._d[k] for k in self.matching_keys(key))

    def __setitem__(self, key, value):
        if not self._checkstar(key):
            self._d[key] = value
        else:
            for k in self.matching_keys(key):
                self._d[k] = value

    def __delitem__(self, key):
        if not self._checkstar(key):
            del self._d[key]
        else:
            for k in self._getmatching(key):
                del self._d[k]

    def __len__(self):
        return len(self._d)

    def __contains__(self, key):
        return bool(self.matching_keys(key))

    def __iter__(self):
        yield from self._d

    def __repr__(self):
        c = ['{}: {}'.format(k, v) for k,v in self._d.items()]
        return 'SelectDict({' + ', '.join(c) + '})'

    @class_property
    def STAR(cls):
        return cls._STAR

    def matching_keys(self, pattern):
        return SelectDict_matching_keys(self, pattern)
