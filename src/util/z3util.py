import z3
import operator
import functools as ft


def hamming_a(bv):
    s = bv.size()
    return z3.Sum([(bv >> i) & 1 for i in range(s)])

# faster than a
def hamming_b(bv):
    s = bv.size().bit_length()
    return z3.Sum([z3.ZeroExt(s, z3.Extract(i,i,bv)) for i in range(bv.size())])

# faster than b
def hamming_c(bv):
    '''
    Based on popcount64a from https://en.wikipedia.org/wiki/Hamming_weight

    Operation:
        Basic idea is take the sum of the even and odd bits,
        hamming = (bv & (01)*) + ((bv & (10)*) >> 1)
        We now have hamming weight of each bit pair,
        next take the sum of the even and odd pairs
        hamming = (hamming & (0011)*) + ((hamming & (1100)*) >> 2)
        we now have the weight of each group of 4
    '''

    #Next power of 2 bits
    bsize = bv.size()
    s = 2**((bsize - 1).bit_length())

    max_exp = (s - 1).bit_length()
    mvals = [(2**i, build_grouped_mask(2**i, bsize).value) for i in range(max_exp)]
    return ft.reduce(lambda x, m: (x & m[1]) + (z3.LShR(x, m[0]) & m[1]), mvals, bv)

# possibly marginally faster than c
def hamming_d(bv):
    '''
    Based on popcount64b from https://en.wikipedia.org/wiki/Hamming_weight

    Operation:
        Same as hamming_c except eventual we can guarantee that top bits are always
        0 so hamming & (1{k}0{k}) == 0, hence don't bother summing the odds.
        Further if hamming & (1{k}0{k}) == 0 then hamming & (0{k}1{k}) == hamming
        so don't bother masking at all.
    '''
    bsize = bv.size()
    b_point = bsize.bit_length()

    s = 2**((bsize - 1).bit_length())

    max_exp = (s - 1).bit_length()
    mvals = [(2**i, build_grouped_mask(2**i, bsize).value) for i in range(max_exp)]
    x = bv - (z3.LShR(bv, mvals[0][0]) & mvals[0][1])
    x = (x & mvals[1][1]) + (z3.LShR(x, mvals[1][0]) & mvals[1][1])

    for idx,i in enumerate(mvals[2:]):
        x = (x + z3.LShR(x, i[0])) & i[1]
        if i[0] > b_point:
            break

    if len(mvals) >= 3:
        for i in mvals[idx+3:]:
            x += z3.LShR(x, i[0])

    return x & (2**b_point - 1)

hamming = hamming_d


def absolute_value(bv):
    '''
    Based on: https://graphics.stanford.edu/~seander/bithacks.html#IntegerAbs

    Operation:
        Desired behavior is by definition (bv < 0) ? -bv : bv
        Now let mask := bv >> (bv.size() - 1)
        Note because of sign extension:
            bv >> (bv.size() - 1) == (bv < 0) ? -1 : 0

        Recall:
            -x == ~x + 1 => ~(x - 1) == -(x - 1) -1 == -x
            ~x == -1^x
             x ==  0^x

        now if bv < 0 then -bv == -1^(bv - 1) == mask ^ (bv + mask)
        else bv == 0^(bv + 0) == mask^(bv + mask)
        hence for all bv, absolute_value(bv) == mask ^ (bv + mask)
    '''
    mask = bv >> (bv.size() - 1)
    return mask ^ (bv + mask)


#used in testing
_GIANT_NUMBER = 5016456510113118655434598811035278955030765345404790744303017523831112055108147451509157692220295382716162651878526895249385292291816524375083746691371804094271873160484737966720260389217684476157468082573 * 14197795064947621068722070641403218320880622795441933960878474914617582723252296732303717722150864096521202355549365628174669108571814760471015076148029755969804077320157692458563003215304957150157403644460363550505412711285966361610267868082893823963790439336411086884584107735010676915

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
            val_size = value.size
            value = value.value

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

    @property
    def hamming(self): return sum(i for i in self)

    def to_formatted_string(self, init_f=None, pre_f=None, elem_f=None, post_f=None, final_f=None):
        if pre_f is None:
            pre_f = lambda *x: ''

        if elem_f is None:
            elem_f = lambda size, value, idx, v: str(v)

        if post_f is None:
            post_f = lambda *x: ''

        s = []
        if init_f is not None:
            s.append(init_f(self.size, self.value))

        for idx, v in enumerate(self):
            s.append(pre_f(self.size, self.value, idx, v))
            s.append(elem_f(self.size, self.value, idx, v))
            s.append(post_f(self.size, self.value, idx, v))

        if final_f is not None:
            s.append(final_f(self.size, self.value))

        return ''.join(s)

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
        elif value in Mask._one_vals:
            self.value |= 1 << (self.size-idx-1)
        else:
            raise ValueError()


    def __repr__(self): return ''.join('1' if i == 1 else '0' for i in self)

    def __hash__(self): return 7*hash(self.value) + 13*hash(self.size)
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

