import itertools as it
import functools as ft
import math
import z3
import z3util as zu



def place_constraints(comps, fab_dims, wire_lengths, pack=True):
    '''
        place_constraints :: {Component} -> (int, int) -> [int] -> Bool? -> z3.z3.BoolRef
    '''
    nnode = len(comps)

    frows, fcols = fab_dims

    constraints = []
    if pack:
        def _get_x(bv): return z3.Extract(frows+fcols-1, frows, bv)
        def _get_y(bv): return z3.Extract(frows-1, 0, bv)
        for comp in comps: comp.pos = z3.BitVec(comp.name, frows+fcols)
        constraints.append(z3.Distinct(*(c.pos for c in comps)))

    else:
        def _get_x(bv): return bv[0]
        def _get_y(bv): return bv[1]
        for comp in comps: comp.pos = (z3.BitVec(comp.name + '_x', frows), z3.BitVec(comp.name + '_y', fcols))
        constraints.append(z3.Distinct(*(z3.Concat(c.pos[0], c.pos[1]) for c in comps)))

    for comp in comps:
        for adj in comp.inputs:
            #should dispatch to fabric to get the rules
            c = []
            for wl in wire_lengths:
                #should probably be comp.pos & (shifted adj.pos) != 0,
                #so that components can have variable size
                c.append(z3.Or(
                        z3.And(_get_x(comp.pos) == z3.LShR(_get_x(adj.pos), wl) , _get_y(comp.pos) == _get_y(adj.pos)),
                        z3.And(_get_x(comp.pos) == _get_x(adj.pos) << wl        , _get_y(comp.pos) == _get_y(adj.pos)),
                        z3.And(_get_y(comp.pos) == z3.LShR(_get_y(adj.pos), wl) , _get_x(comp.pos) == _get_x(adj.pos)),
                        z3.And(_get_y(comp.pos) == _get_y(adj.pos) << wl        , _get_x(comp.pos) == _get_x(adj.pos)),
                        ))

            constraints.append(z3.Or(c))

        constraints.append(zu.hamming(_get_x(comp.pos)) == __COMP_X)
        constraints.append(zu.hamming(_get_y(comp.pos)) == __COMP_Y)


    return z3.And(constraints)

def find_shift(x, y, rows, cols):
    '''
        find_bit_num :: z3.BitVec[a] -> z3.BitVec[b] -> int -> int -> z3.BitVec[c]
        Returns a z3.BitVec of size rows*cols that can be used to check that the
        correct bit of the 'one hot' version of the component represented by x
        and y is set
    '''
    n = rows*cols - x.size()
    return z3.ZeroExt(n,y)*cols + z3.ZeroExt(n,x)



def abs_diff(pos1, pos2, fab_dims):
    '''
        abs_diff :: z3.BitVec[a] -> z3.BitVec[a] -> (int, int) - > z3.BitVec[a]
        Takes two z3 BitVec and returns the absolute value of their difference
    '''
    #zero-extend to avoid overflow
    n = fab_dims[0]*fab_dims[1] - pos1.size()
    return z3.If(z3.ULT(pos1, pos2), z3.ZeroExt(n,pos2) - z3.ZeroExt(n,pos1), z3.ZeroExt(n,pos1) - z3.ZeroExt(n,pos2))



def place_constraints_opt(comps, fab_dims, distinct_flag=True):
    '''
        place_constraints_opt :: {Component} -> (int, int) -> [int] -> (z3.z3.BoolRef)
    '''
    rows = fab_dims[0]
    cols = fab_dims[1]
    nnode = len(comps)

    constraints = []
    if distinct_flag:
        c = []
        for comp in comps:
            #add a tuple representing the x,y coordinates
            comp.pos = (z3.BitVec(comp.name + '_x', int(math.ceil(math.log(cols,2)))), z3.BitVec(comp.name + '_y', int(math.ceil(math.log(rows,2)))))
            c.append(z3.Concat(comp.pos[0],comp.pos[1]))
        constraints.append(z3.simplify(z3.Distinct(c), ':blast-distinct', True))
    else:
        onehot_list = []
        for comp in comps:
            comp.pos = (z3.BitVec(comp.name + '_x', int(math.ceil(math.log(cols,2)))), z3.BitVec(comp.name + '_y', int(math.ceil(math.log(rows,2)))))
            #one hot representation -- temporary var
            temp_1h = z3.BitVec(comp.name, rows*cols)
            onehot_list.append(temp_1h)
            constraints.append(zu.hamming(temp_1h) == __COMP_AREA)
            constraints.append(z3.Extract(0,0,z3.LShR(temp_1h,find_shift(comp.pos[0],comp.pos[1],rows,cols))) == 1)

        u = ft.reduce(lambda x,y: x|y, [bv for bv in onehot_list])
        constraints.append(zu.hamming(u) == nnode)

    #check if number of rows/cols is a power of two (and thus placements can be any bit representation), if not, constrain the placements to be on fabric
    if not math.log(rows,2).is_integer() and not math.log(cols,2).is_integer():
        for comp in comps:
            constraints.append(z3.And(z3.ULT(comp.pos[0],cols), z3.ULT(comp.pos[1], rows)))
    elif not math.log(rows,2).is_integer():
        for comp in comps:
            constraints.append(z3.ULT(comp.pos[1], rows))
    elif not math.log(cols,2).is_integer():
        for comp in comps:
            constraints.append(z3.ULT(comp.pos[0], cols))

  #form the manhattan distance
    manhattan_dist = 0
    for comp in comps:
        for adj in comp.inputs:
            manhattan_dist += abs_diff(comp.pos[0], adj.pos[0], fab_dims) + abs_diff(comp.pos[1], adj.pos[1], fab_dims)

    return z3.And(constraints), manhattan_dist

def print_model(model, comps, fab_dims, wire_lengths):
    p2n = {model.evaluate(x.pos).as_long() : str(x.name).strip("'") for x in comps}

    mask, mrows, mcols, mwl = _build_standard_mask(fab_dims, wire_lengths)

    width = 2 + max(len(x) for x in p2n.values())

    s = []
    for i in range(mrows*mcols):
        if mask[i] == 1 and 2**i in p2n:
            s.append('{c: ^{w}}'.format(c=p2n[2**i], w=width))
        elif mask[i] == 1:
            s.append('{c: ^{w}}'.format(c='-', w=width))


        if (i % mcols) == mcols - 1:
            s.append('\n')

    s = ''.join(s)
    print(s)

def print_model_2d(model, comps, fab_dims, wire_lengths, pack=True):
    frows, fcols = fab_dims

    if pack:
        def _get_x(bv): return z3.extract(frows+fcols-1, frows, bv)
        def _get_y(bv): return z3.extract(frows-1, 0, bv)
    else:
        def _get_x(bv): return bv[0]
        def _get_y(bv): return bv[1]


    ps = [(_get_x(c.pos), _get_y(c.pos), str(c.name).strip("'")) for c in comps]
    print(ps)
    p2n = {(model.eval(x).as_long(), model.eval(y).as_long()) : n for x,y,n in ps}
    print(p2n)
    print()

    width = 2 + max(len(x) for x in p2n.values())

    s = []
    for y in range(frows):
        for x in range(fcols):
            print(2**x,2**y)
            if (2**x,2**y) in p2n:
                s.append('{c: ^{w}}'.format(c=p2n[(2**x,2**y)], w=width))
            else:
                s.append('{c: ^{w}}'.format(c='-', w=width))
        s.append('\n')

    s = ''.join(s)
    print(s)

def run_test(adj, fab_dims, wire_lengths={}, debug_prints=True,
        constraints_gen=place_constraints,
        model_checker=None,
        model_printer=print_model
        ):

    comps = build_graph(adj)

    if wire_lengths: #use provided wire lengths
        print('Finding satisfying model with given wire lenths')
        constraints = constraints_gen(comps, fab_dims, wire_lengths)
        s = z3.Solver()
        s.add(constraints)
        if s.check() != z3.sat:
            if debug_prints:
                print('test is unsat')
            return s

        if debug_prints:
            print('test is sat')

        if debug_prints and all(model_checker(s.model(), comps, fab_dims, wire_lengths)):
            model_printer(s.model(), comps, fab_dims, wire_lengths)
            return (True, s)
        elif debug_prints:
            return (False, s)
        elif all(model_checker(s.model(), comps, fab_dims, wire_lengths, printer=lambda *x: None)):
            return (True, s)
        else:
            return (False, s)
    else: #no provided wire lengths, optimize the manhattan distance
        print('No provided wire lengths. Minimizing total L1 norm')
        constraints, manhattan_dist = place_constraints_opt(comps, fab_dims)
        s = z3.Optimize()
        s.add(constraints)
        h = s.minimize(manhattan_dist)

        if s.check() != z3.sat:
            if debug_prints:
                print('test is unsat')
            return s

        if debug_prints:
            print('test is sat')
            print('Total L1 Norm = ', s.lower(h))

        #print(s.model())

        print_model_opt(s.model(), comps, fab_dims)
        return s



def tiny_test(dims=(3,3), debug_prints=True):
    '''
        place 4 nodes on a 3x3 fabric [with length 1 wires]
    '''
    adj = {'n1' : {'n2','n3'}, 'n2' : {'n4'}, 'n3' : {'n4'}, 'n4' : {}}
    run_test(adj, dims, {}, debug_prints)


def small_test(dims=(8,8), debug_prints=True):
    '''
        place a depth 5 binary tree on a 8 by 8 [with length 2,3 wires]
    '''
    adj = {'n{}'.format(i) : frozenset(('n{}'.format(2*i), 'n{}'.format(2*i+1))) for i in range(1,2**4)}
    run_test(adj, dims, {}, debug_prints)


def unsat_test(debug_prints=True):
    adj = {'n1' : {'n2','n3','n4','n5','n6'}}
    run_test(adj, (4,4), {1}, debug_prints)

