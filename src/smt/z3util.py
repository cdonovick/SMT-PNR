import z3
import operator
import functools as ft
from smt_switch import functions
from util import Mask, build_grouped_mask

And = functions.And()
lshr = functions.bvlshr()


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
    bsize = bv.sort.width
    b_point = bsize.bit_length()

    s = 2**((bsize - 1).bit_length())

    max_exp = (s - 1).bit_length()
    mvals = [(2**i, build_grouped_mask(2**i, bsize).value) for i in range(max_exp)]
    x = bv - (lshr(bv, mvals[0][0]) & mvals[0][1])
    x = (x & mvals[1][1]) + (lshr(x, mvals[1][0]) & mvals[1][1])

    for idx,i in enumerate(mvals[2:]):
        x = (x + lshr(x, i[0])) & i[1]
        if i[0] > b_point:
            break

    if len(mvals) >= 3:
        for i in mvals[idx+3:]:
            x += lshr(x, i[0])

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
    mask = bv >> (bv.sort.width - 1)
    return mask ^ (bv + mask)


#used in testing
_GIANT_NUMBER = 5016456510113118655434598811035278955030765345404790744303017523831112055108147451509157692220295382716162651878526895249385292291816524375083746691371804094271873160484737966720260389217684476157468082573 * 14197795064947621068722070641403218320880622795441933960878474914617582723252296732303717722150864096521202355549365628174669108571814760471015076148029755969804077320157692458563003215304957150157403644460363550505412711285966361610267868082893823963790439336411086884584107735010676915

