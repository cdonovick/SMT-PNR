import z3
import operator

def hamming(bv):
    s = bv.size().bit_length()
    return z3.Sum([z3.ZeroExt(s, z3.Extract(i,i,bv)) for i in range(bv.size())])

class Mask:
    '''
        Over engineered class for building bit masks
    '''
    class mask_iter:
        def __init__(self, mask): 
            self.__mask = mask
            self.__idx = mask.size
            
        def __iter__(self): 
            return self

        def __next__(self):
            if self.__idx > 0:
                self.__idx -= 1
                return (self.__mask.value >> self.__idx) & 1
            raise StopIteration()


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

    def __init__(self, value=None, size=None, truncate=True):
        if isinstance(value, type(self)):
            value = value.value
            val_size = value.size

        elif isinstance(value, int):
            val_size = value.bit_length()

        elif hasattr(value, '__iter__'):
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

        elif not truncate:
            size = max(size, val_size)

        self._intmask = 2**size - 1
        self._value = value & self._intmask 
        self._size = size
    
    @property
    def value(self): return self._value

    @property
    def size(self): return self._size

    @value.setter
    def value(self, value):
        if isinstance(value, type(self)):
            value = value.value
        elif hasattr(value, '__iter__'):
            value, _ = Mask._iter2int(value)
        elif not isinstance(value, int):
            raise ValueError("Use of type {} as value is undefined".format(type(value)))

        self._value = value & self._intmask 

    @size.setter
    def size(self, size):
        self._size = size
        self._intmask = 2**size - 1
        #truncate value
        self._value &= self._intmask 

    def __iter__(self): return Mask.mask_iter(self)
    
    def __getitem__(self, idx):
        if idx >= self.size:
            raise IndexError()
        else:
            return (self.value >> (self.size - idx - 1)) & 1

    def __setitem__(self, idx, value):
        if idx >= self.size:
            raise IndexError()
        if value in Mask._zero_vals:
            self.value &= ~(1 << (self.size-idx-1))
        elif value in Maske._one_vals:
            self.value |= 1 << (self.size-idx-1)
        else:
            raise ValueError()


    def __repr__(self): return ''.join('1' if i == 1 else '0' for i in self)


    def __hash__(self): return hash(self.value)
    def __int__(self):  return int(self.value)

    def __neg__(self):    return Mask(value=-self.value     & self._intmask, size=self.size)
    def __abs__(self):    return Mask(value=abs(self.value) & self._intmask, size=self.size)
    def __invert__(self): return Mask(value=~self.value     & self._intmask, size=self.size)

    def _make_bin_op(op):
        def bin_op(self, other):
            if isinstance(other, type(self)):
                return type(self)(value=op(self.value, other.value), size=self.size, truncate=True)
            elif isinstance(other, int):
                return type(self)(value=op(self.value, other), size=self.size, truncate=True)
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

    def _make_bool_op(op):
        def bool_op(self, other):
            if isinstance(other, type(self)):
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

    __lt__ = _make_bool_op(operator.lt)
    __le__ = _make_bool_op(operator.le)
    __eq__ = _make_bool_op(operator.eq)
    __ne__ = _make_bool_op(operator.ne)
    __gt__ = _make_bool_op(operator.gt)
    __ge__ = _make_bool_op(operator.ge)

