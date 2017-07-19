from collections.abc import MutableMapping, Set
from .setlist import SetList
from util import class_property, FlyWeightMeta

__all__ = ['SelectDict', 'STAR']

class _STAR(metaclass=FlyWeightMeta):
    __slots__ = ()

    def __eq__(self, other):
        return True

STAR = _STAR()

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

    def _getmatching(self, key):
        return [k for k in self._d if k == key]

    def __getitem__(self, key):
        if not self._checkstar(key):
            return self._d[key]
        else:
            return SetList(self._d[k] for k in self._getmatching(key))

    def __setitem__(self, key, value):
        if not self._checkstar(key):
            self._d[key] = value
        else:
            for k in self._getmatching(key):
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
        return bool(self._getmatching(key))

    def __iter__(self):
        yield from self._d

    def __repr__(self):
        c = ['{}: {}'.format(k, v) for k,v in self._d.items()]
        return 'SelectDict({' + ', '.join(c) + '})'

    @class_property
    def STAR(cls):
        return cls._STAR



class DefaultSelectDict(SelectDict):
    def __init__(self, default):
        self._default = default
        super().__init__()

    def __getitem__(self, key):
        if key not in self._d:
            super(DefaultSelectDict, self).__setitem__(key, self._default())

        # now call the super's getitem
        return super(DefaultSelectDict, self).__getitem__(key)

#testing stuff
#
#from collections import namedtuple
#import random
#import itertools
#import time
#import sys
#
#def test(T, n, k):
#    dl = [I() for I in T]
#    s_fields = ['f{}'.format(i) for i in range(k)]
#    key_types = []
#    for l in range(1,len(s_fields) + 1):
#        for s in itertools.combinations(s_fields, l):
#            key_types.append(namedtuple(''.join(s), s))
#
#    for _ in range(int(n**(1/2))):
#        k_t = random.choice(key_types)
#        args = []
#        args = {k : random.randrange(int(n**(1/2))) for k in k_t._fields}
#        k = k_t(**args)
#        v = random.randrange(n)
#        for d in dl:
#            d[k] = v
#
#    for _ in range(n):
#        if random.randint(0,1):
#            k_t = random.choice(key_types)
#            args = {k : random.randrange(int(n**(1/2))) for k in k_t._fields}
#            k = k_t(**args)
#            v = random.randrange(n)
#            for d in dl:
#                d[k] = v
#        else:
#            r = []
#            k = random.choice(list(dl[-1].keys()))
#            for d in dl:
#                r.append(d[k])
#
#            for r1 in r:
#                for r2 in r:
#                    assert r1 == r2
#
#    for _ in range(int(n**(1/2))):
#        k = random.choice(list(dl[-1].keys()))
#        for d in dl:
#            del d[k]
#
#    for d1 in dl:
#        for d2 in dl:
#            if isinstance(d1, dict) and isinstance(d2, dict):
#                assert d1 == d2
#            elif isinstance(d1, dict):
#                assert d1 == d2._d
#            elif isinstance(d2, dict):
#                assert d1._d == d2
#            else:
#                assert d1._d == d2._d
#
#def star_test(T, n, k):
#    dl = [I() for I in T]
#    s_fields = ['f{}'.format(i) for i in range(k)]
#    k_t = namedtuple('Idx_t', s_fields)
#
#    for _ in range(n):
#        args = []
#        args = {k : random.randrange(int(n**(1/2))) for k in k_t._fields}
#        k = k_t(**args)
#        v = random.randrange(n)
#        for d in dl:
#            d[k] = v
#
#    for _ in range(int(n**(1/2))):
#        if random.randint(0,1):
#            args = {k : random.randrange(int(n**(1/2))) for k in k_t._fields}
#            s_arg = random.choice(k_t._fields)
#            v = random.randrange(n)
#            for d in dl:
#                args[s_arg] = d.STAR
#                k = k_t(**args)
#                d[k] = v
#        else:
#            r = []
#            k = random.choice(list(dl[-1].keys()))
#            s_arg = random.choice(k._fields)
#            for d in dl:
#                k = k._replace(**{s_arg : d.STAR})
#                r.append(d[k])
#
#            for r1 in r:
#                for r2 in r:
#                    assert r1 == r2, '{}\n{}'.format(set.union({(v, '1') for v in r1 if v not in r2}, {(v, '2') for v in r2 if v not in r1}), r1&r2)
#
#    for _ in range(int(n**(1/16))):
#        k = random.choice(list(dl[-1].keys()))
#        s_arg = random.choice(k._fields)
#        for d in dl:
#            k = k._replace(**{s_arg : d.STAR})
#            del d[k]
#
#
#    for d1 in dl:
#        for d2 in dl:
#            assert d1._d == d2._d
#
#def weighted_choice(choices):
#    total = sum(w for _, w in choices)
#    r = random.uniform(0, total)
#    idx = 0
#    for c,w in choices:
#        if idx+w >= r:
#            return c
#        idx += w
#
#
#def getsize(obj_0):
#    """Recursively iterate to sum size of object & members."""
#    from numbers import Number
#    from collections import Set, Mapping, deque
#
#    zero_depth_bases = (str, bytes, Number, range, bytearray)
#    iteritems = 'items'
#    def inner(obj, _seen_ids = set()):
#        obj_id = id(obj)
#        if obj_id in _seen_ids:
#            return 0
#        _seen_ids.add(obj_id)
#        size = sys.getsizeof(obj)
#        if isinstance(obj, zero_depth_bases):
#            pass # bypass remaining control flow and return
#        elif isinstance(obj, (tuple, list, Set, deque)):
#            size += sum(inner(i) for i in obj)
#        elif isinstance(obj, Mapping) or hasattr(obj, iteritems):
#            size += sum(inner(k) + inner(v) for k, v in getattr(obj, iteritems)())
#        # Check for custom object instances - may subclass above too
#        if hasattr(obj, '__dict__'):
#            size += inner(vars(obj))
#        if hasattr(obj, '__slots__'): # can have __slots__ with __dict__
#            size += sum(inner(getattr(obj, s)) for s in obj.__slots__ if hasattr(obj, s))
#        return size
#    return inner(obj_0)
#
#def speed_test(T, n, k):
#    op_w = [
#            ('set' , 3),
#            ('get' , 3),
#            ('del' , 1),
#    ]
#
#    call = {
#            'set' : lambda d,k,v : d.__setitem__(k, v),
#            'get' : lambda d,k,v : d.__getitem__(k),
#            'del' : lambda d,k,v : d.__delitem__(k),
#    }
#
#    s_w = [(i , 2**(k - i)) for i in range(k//2)]
#
#
#    dl = [I() for I in T]
#    s_fields = ['f{}'.format(i) for i in range(k)]
#    k_t = namedtuple('Idx_t', s_fields)
#    ops = []
#    keys = []
#    stars = []
#    vals = []
#
#
#    for _ in range(int(n**(1/2))):
#        ops.append('set')
#
#    for _ in range(n):
#        ops.append(weighted_choice(op_w))
#
#    for op in ops:
#        if op == 'set':
#            k = k_t(**{k : random.randrange(int(n**(1/2))) for k in k_t._fields})
#            keys.append(k)
#        else:
#            keys.append(None)
#
#        ns = weighted_choice(s_w)
#
#        stars.append(random.sample(k_t._fields, ns))
#        vals.append(random.randrange(n))
#
#    key_sim = []
#    for i,key in enumerate(keys):
#        if key is None:
#            k = random.choice(key_sim)
#            keys[i] = k
#            if ops[i] == 'del':
#                key_sim.remove(k)
#        else:
#            key_sim.append(key)
#
#    results = []
#    for d in dl:
#        for i,s in enumerate(stars):
#            keys[i] = keys[i]._replace(**{f : d.STAR for f in s})
#        start = time.time()
#        for op, k, v in zip(ops, keys, vals):
#            try:
#                call[op](d,k,v)
#            except KeyError:
#                pass
#        end = time.time()
#        results.append((type(d), end-start, getsize(d)))
#
#    for d1 in dl:
#        for d2 in dl:
#            assert d1._d == d2._d
#    return results
#
#test([SelectDict, SelectDict2, dict],  10000, 5)
#star_test([SelectDict, SelectDict2],   10000, 5)
#def print_res(rx):
#    min_mem = float('inf')
#    min_tim = float('inf')
#    for r in rx:
#        if r[1] < min_tim:
#            min_tim_obj = r
#            min_tim     = r[1]
#        elif r[1] == min_tim and r[2] < min_tim_obj[2]:
#            min_tim_obj = r
#
#        if r[2] < min_mem:
#            min_mem_obj = r
#            min_mem     = r[2]
#        elif r[2] == min_mem and r[1] < min_mem_obj[1]:
#            min_mem_obj = r
#
#    print("Best time:  ", min_tim_obj)
#    print("Best space: ", min_mem_obj)
#
#r1 = speed_test([SelectDict, SelectDict2],  100000, 3)
#print_res(r1)
#r2 = speed_test([SelectDict, SelectDict2],  100000, 4)
#print_res(r2)
#r3 = speed_test([SelectDict, SelectDict2],  100000, 5)
#print_res(r3)
#r4 = speed_test([SelectDict, SelectDict2],  100000, 6)
#print_res(r4)
#r5 = speed_test([SelectDict, SelectDict2],  100000, 7)
#print_res(r5)
#
#assert 0
>>>>>>> 84b4754... Optimize SelectDict
