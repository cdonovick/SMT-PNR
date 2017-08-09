import operator
import functools as ft
from collections import Iterable

def build_grouped_mask(k, n):
    '''
    build_grouped_mask :: int -> int -> Mask
    returns the unique mask m of length n that matches the following RE
    ((0{0,k} 1{k}) | (1{0,k})) (0{k} 1{k})*

    '''
    m = Mask(value=k*[0] + k*[1], size=n)
    c = 2*k
    while c < n:
        m |= m << c
        c *= 2
    return m

class Mask:
    '''
        Over engineered class for building bit masks
    '''
    class mask_iter:
        def __init__(self, mask, reversed=False):
            self.__mask = mask
            if reversed:
                self.__idx  = mask.size - 1
                self.__step = -1
            else:
                self.__idx  = 0
                self.__step = 1

        def __iter__(self):
            return self

        def __next__(self):
            try:
                r = self.__mask[self.__idx]
            except IndexError:
                raise StopIteration()

            self.__idx += self.__step
            return r

    _zero_vals = frozenset({0, '0', False})
    _one_vals = frozenset({1, '1', True})

    def _iter2int(iter):
        v = 0
        for size, b in enumerate(iter):
            v <<= 1
            if b in Mask._one_vals:
                v |= 1
            elif b not in Mask._zero_vals:
                raise ValueError('value must be composed of bits')
        return v, size+1

    def __init__(self, value=None, size=None, MSB0=True):
        if isinstance(value, type(self)):
            val_size = value.size
            value = value.value

        elif isinstance(value, int):
            val_size = value.bit_length()

        elif isinstance(value, Iterable):
            value, val_size = Mask._iter2int(value)

        elif value is None:
            if size is None:
                raise ValueError("Either value or size must be specified")
            value = 0
            val_size = size

        else:
            raise ValueError("Use of type {} as value is undefined".format(type(value)))

        if size is None:
            size = val_size

        #needed for size setter
        self._value = 0
        self.size = size
        self.value = value
        self.MSB0 = MSB0

    @property
    def value(self): return self._value

    @property
    def size(self): return self._size

    @value.setter
    def value(self, value):
        if isinstance(value, type(self)):
            value = value.value

        elif isinstance(value, Iterable):
            value, _ = Mask._iter2int(value)

        elif not isinstance(value, int):
            raise ValueError("Use of type {} as value is undefined".format(type(value)))

        self._value = value & self._intmask

    @size.setter
    def size(self, size):
        self._size = size
        self._intmask = 2**size - 1
        #truncate value
        self.value &= self._intmask

    @property
    def hamming(self): return sum(i for i in self)

    @property
    def MSB0(self):
        return self._MSB0

    @MSB0.setter
    def MSB0(self, MSB0):
        if MSB0:
            self._idx_func = lambda idx : self.size - idx - 1
        else:
            self._idx_func = lambda idx : idx

        self._MSB0 = MSB0

    def __iter__(self): return Mask.mask_iter(self, False)
    def __reversed__(self): return Mask.mask_iter(self, True)

    def __getitem__(self, idx):
        if isinstance(idx, slice):
            if idx.step is None:
                step = 1
            else:
                step = idx.step

            if step < 0:
                start = min(idx.start or self.size - 1, self.size - 1)
                stop = max(idx.stop or -1, -1)
            elif step > 0:
                start = max(idx.start or 0, 0)
                stop = min(idx.stop or self.size, self.size)
            else:
                raise ValueError('slice step cannot be 0')

            idx_list = list(range(start, stop, step))

            return type(self)(value=(self[i] for i in idx_list), size=len(idx_list), MSB0=self.MSB0)

        if not (0 <= idx < self.size):
            raise IndexError()

        return (self.value >> self._idx_func(idx)) & 1

    def __setitem__(self, idx, value):
        if isinstance(idx, slice):
            if idx.step is None:
                step = 1
            else:
                step = idx.step

            if step < 0:
                start = min(idx.start or self.size - 1, self.size - 1)
                stop = max(idx.stop or -1, -1)
            elif step > 0:
                start = max(idx.start or 0, 0)
                stop = min(idx.stop or self.size, self.size)
            else:
                raise ValueError('slice step cannot be 0')

            idx_list = list(range(start, stop, step))

            if isinstance(value, Iterable):
                val_list = [v for v in value]
            elif isinstance(value, int):
                val_list = [v for v in Mask(value, size=len(idx_list))]
            else:
                val_list = [value]*len(idx_list)

            if len(idx_list) != len(val_list):
                raise ValueError('Cannot broadcast a value of size {} onto a slice of size {}'.format(len(val_list), len(idx_list)))

            for i,v in zip(idx_list, val_list):
                self[i] = v

            return

        if not (0 <= idx < self.size):
            raise IndexError()

        if value in Mask._zero_vals:
            self.value &= ~(1 << self._idx_func(idx))
        elif value in Mask._one_vals:
            self.value |=  (1 << self._idx_func(idx))
        else:
            raise ValueError()


    def __repr__(self): return 'Mask(value={}, size={}, MSB0={})'.format(self.value, self.size, self.MSB0)
    def __str__(self): return ''.join('1' if i == 1 else '0' for i in (self if self.MSB0 else reversed(self)))

    def __hash__(self): return 7*hash(self.value) + 13*hash(self.size)
    def __int__(self):  return int(self.value)

    def __neg__(self):    return type(self)(value=-self.value    , size=self.size, MSB0=self.MSB0)
    def __abs__(self):    return type(self)(value=abs(self.value), size=self.size, MSB0=self.MSB0)
    def __invert__(self): return type(self)(value=~self.value    , size=self.size, MSB0=self.MSB0)

    def _make_bin_op(op):
        def bin_op(self, other):
            if isinstance(other, type(self)):
                return type(self)(value=op(self.value, other.value), size=self.size, MSB0=self.MSB0)
            elif isinstance(other, int):
                return type(self)(value=op(self.value, other)      , size=self.size, MSB0=self.MSB0)
            else:
                raise TypeError()
        return bin_op

    def _make_ibin_op(op):
        def ibin_op(self, other):
            if isinstance(other, type(self)):
                self.value = op(self.value, other.value)
            elif isinstance(other, int):
                self.value = op(self.value, other)
            else:
                raise TypeError()
            return self
        return ibin_op

    def _make_bool_op(op, size_diff):
        def bool_op(self, other):
            if isinstance(other, type(self)):
                if self.size != other.size:
                    return size_diff
                else:
                    return op(self.value, other.value)
            elif isinstance(other, int):
                return op(self.value, other)
            else:
                raise TypeError()
        return bool_op

    __add__ = _make_bin_op(operator.add)
    __sub__ = _make_bin_op(operator.sub)
    __mul__ = _make_bin_op(operator.mul)
    __mod__ = _make_bin_op(operator.mod)
    __lshift__ = _make_bin_op(operator.lshift)
    __rshift__ = _make_bin_op(operator.rshift)
    __and__ = _make_bin_op(operator.and_)
    __or__ = _make_bin_op(operator.or_)
    __xor__ = _make_bin_op(operator.xor)

    __iadd__ = _make_ibin_op(operator.iadd)
    __isub__ = _make_ibin_op(operator.isub)
    __imul__ = _make_ibin_op(operator.imul)
    __imod__ = _make_ibin_op(operator.imod)
    __ilshift__ = _make_ibin_op(operator.ilshift)
    __irshift__ = _make_ibin_op(operator.irshift)
    __iand__ = _make_ibin_op(operator.iand)
    __ior__ = _make_ibin_op(operator.ior)
    __ixor__ = _make_ibin_op(operator.ixor)


    __eq__ = _make_bool_op(operator.eq, False)
    __ne__ = _make_bool_op(operator.ne, True)

