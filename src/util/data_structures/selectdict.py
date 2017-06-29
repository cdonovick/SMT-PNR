from collections import defaultdict
from collections.abc import  MutableMapping
from .multidict import MultiDict
from .setlist import SetList

__all__ = ['SelectDict']

class SelectDict(MutableMapping):
    def __init__(self, d=dict()):
        self._d = dict()
        self._keymap = defaultdict(MultiDict)
        for k,v in d.items():
            self[k] = v

    def __getitem__(self, key):
        c = set(self._d.keys())
        for k,v in key._asdict().items():
            if v is not None:
                c.intersection_update(self._keymap[k][v])

        return SetList(self._d[k] for k in c)

    def __setitem__(self, key, value):
        for k,v in key._asdict().items():
            if v is not None:
                self._keymap[k][v] = key

        self._d[key] = value

    def __delitem__(self, key):
        for k, v in key._asdict().items():
            if v is not None:
                del self._keymap[k][v]

        del self._d[key]

    def __len__(self):
        return len(self._d)

    def __contains__(self, key):
        return key in self._d

    def __iter__(self):
        yield from self._d

    def __repr__(self):
        c = ['{}: {}'.format(k, v) for k,v in self._d.items()]
        return 'SelectDict({' + ', '.join(c) + '})'
