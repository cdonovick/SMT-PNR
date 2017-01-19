import itertools as it
import functools as ft
import math
import z3
import z3util as zu

class Component:
    def __init__(self, name, inputs=(), outputs=()):
        self._name = name
        self._inputs = set(inputs)
        self._outputs = set(outputs)
        self.pos = None

    @property
    def name(self):
        return self._name

    @property
    def inputs(self):
        return (i for i in self._inputs)
    
    @property
    def outputs(self):
        return (i for i in self._outputs)

    def extend_inputs(self, comps):
        self._inputs.update(comps)

    def extend_outputs(self, comps):
        self._outputs.update(comps)

    def add_input(self, comp):
        self._inputs.add(comp)

    def add_output(self, comp):
        self._outputs.add(comp)

    def __hash__(self):
        return hash(self.name)

    def __repr__(self):
        return 'name: {}, inputs: {}, outputs: {}'.format(self.name, {x.name for x in self.inputs}, {x.name for x in self.outputs})

        
__COMP_X    = 1
__COMP_Y    = 1
__COMP_AREA = __COMP_X * __COMP_Y


def build_graph(adj_dict): 
    '''
        build_graph :: Hash T, repr T => {T->[T]}->{Component}
        adj_dict[x] :: the out edges of x
    '''
    d = dict()

    for x, adj in adj_dict.items():
        if isinstance(x, str):
            xf = x
        else:
            xf = repr(x)

        if xf not in d:
            d[xf] = Component(xf)

        for y in adj:
            if isinstance(y, str):
                yf = y
            else:
                yf = repr(y)

            if yf not in d:
                d[yf] = Component(yf)

            d[xf].add_output(d[yf])
            d[yf].add_input(d[xf])

    return d.values()


def _build_standard_mask(fab_dims, wire_lengths):
    '''
        _build_standard_mask :: (int, int) -> [int] -> (Mask, int, int, int)
        The return value is MASK, MASK_ROWS, MASK_COLS, MWL where

        MASK:=
               MWL   COLS   MWL
              0...0 1....1 0...0
                .            .
        ROWS    .            .
                .            .
              0...0 1....1 0...0
    
        MWL := max(wire_lengths)
        ROWS := fab_dims[0]
        COLS := fab_dims[1]
        MASK_ROWS := ROWS
        MASK_COLS := MWL + COLS + MWL
    '''
    mwl = max(wire_lengths)

    mrows = fab_dims[0]
    mcols = fab_dims[1] + 2*mwl

    mask = zu.Mask(value=[0]*mwl + [1]*fab_dims[1] + [0]*mwl, size=mrows*mcols)
    for i in range(mrows.bit_length()):
        mask |= mask << (mcols * 2**i)

    return mask, mrows, mcols, mwl 


def place_constraints(comps, fab_dims, wire_lengths):
    '''
        place_constraints :: {Component} -> (int, int) -> [int] -> z3.z3.BoolRef
    '''
    nnode = len(comps)

    #build bit mask
    mask, mrows, mcols, mwl = _build_standard_mask(fab_dims, wire_lengths)
    
    #print bitmask
    #for idx, v in enumerate(mask):
    #    print(v, end='')
    #    if (idx % mcols) == mcols - 1:
    #        print()


    imask = int(~mask)
    mask = int(mask)


    for comp in comps:
        comp.pos = z3.BitVec(comp.name, mrows*mcols)

    constraints = []
    for comp in comps:
        for adj in comp.inputs:
            #should dispatch to fabric to get the rules
            c = []
            for wl in wire_lengths:
                #should probably be comp.pos & (shifted adj.pos) != 0,
                #so that components can have variable size
                c.append(z3.Or(
                        comp.pos == z3.LShR(adj.pos, wl),
                        comp.pos == adj.pos << wl,
                        comp.pos == z3.LShR(adj.pos, wl*mcols),
                        comp.pos == adj.pos << wl*mcols,
                        ))

            constraints.append(z3.Or(c))

        constraints.append(zu.hamming(comp.pos) == __COMP_AREA)
        #The following is insufficient to achieve the previous
        #constraints.append(comp.pos != 0)

        constraints.append(comp.pos & imask == 0)

    u = ft.reduce(lambda x,y: x|y, [c.pos for c in comps])
    constraints.append(zu.hamming(u) == nnode)

    return z3.And(constraints)

def place_constraints_2d(comps, fab_dims, wire_lengths, pack=True):
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
        constraints.append(z3.simplify(z3.Distinct(*(c.pos for c in comps)),':blast-distinct',True))

    else:
        def _get_x(bv): return bv[0]
        def _get_y(bv): return bv[1]
        for comp in comps: comp.pos = (z3.BitVec(comp.name + '_x', frows), z3.BitVec(comp.name + '_y', fcols))
        constraints.append(z3.simplify(z3.Distinct(*(z3.Concat(c.pos[0], c.pos[1]) for c in comps)),':blast-distinct',True))

    for comp in comps:
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

def print_model_2d(model, comps, fab_dims, wire_lengths):
    frows, fcols = fab_dims

    def _get_x(bv):
        return z3.Extract(frows+fcols-1, frows, bv)

    def _get_y(bv):
        return z3.Extract(frows-1, 0, bv)

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

def print_model_2x(model, comps, fab_dims, wire_lengths):
    frows, fcols = fab_dims

    ps = [(c.pos[0], c.pos[1], str(c.name).strip("'")) for c in comps]
    print(ps)
    p2n = {(model.eval(x).as_long(), model.eval(y).as_long()) : n for x,y,n in ps}
    print(p2n)
    print()

    width = 2 + max(len(x) for x in p2n.values())

    s = []
    for y in range(frows):
        for x in range(fcols):
            if (2**x,2**y) in p2n:
                s.append('{c: ^{w}}'.format(c=p2n[(2**x,2**y)], w=width))
            else:
                s.append('{c: ^{w}}'.format(c='-', w=width))
        s.append('\n')

    s = ''.join(s)
    print(s)


def print_model_opt(model, comps, fab_dims):
    p2n = {(model.evaluate(comp.pos[0]).as_long(), model.evaluate(comp.pos[1]).as_long()): str(comp.name).strip("'") for comp in comps}

    rows = fab_dims[0]
    cols = fab_dims[1]

    width = 2 + max(len(x) for x in p2n.values())

    s = []
    for j in range(rows-1,-1,-1):
        for i in range(cols):
            if (i,j) in p2n:
                s.append('{c: ^{w}}'.format(c=p2n[(i,j)], w=width))
            else:
                s.append('{c: ^{w}}'.format(c='-', w=width))
        s.append('\n')

    s = ''.join(s)
    print(s)


def run_test(adj, fab_dims, wire_lengths={}, debug_prints=True, 
        constraints_gen=place_constraints_2d,
        model_checker=None, 
        model_printer=print_model_2d
        ):

    comps = build_graph(adj)

    if wire_lengths: #use provided wire lengths
        print('Finding satisfying model with given wire lenths')
        frows, fcols = fab_dims
        def _get_x(bv): return z3.Extract(frows+fcols-1, frows, bv)
        def _get_y(bv): return z3.Extract(frows-1, 0, bv)
        #def _get_x(bv): return bv[0]
        #def _get_y(bv): return bv[1]
        constraints = constraints_gen(comps, fab_dims, wire_lengths)
        s = z3.Optimize()
        #z3.set_param("timeout",120000)
        #z3.set_param(verbose=10)
        s.add(constraints)
        wire_lengths = sorted(wire_lengths)
        for comp in comps:
            for adj in comp.inputs:
                #should dispatch to fabric to get the rules
                w = len(wire_lengths)
                s.add_soft(z3.Xor(_get_x(comp.pos) == _get_x(adj.pos), _get_y(comp.pos) == _get_y(adj.pos)),str(w+1))
                for wl in wire_lengths:
                    #should probably be comp.pos & (shifted adj.pos) != 0,
                    #so that components can have variable size
                    zx = z3.Or(
                        _get_x(comp.pos) == z3.LShR(_get_x(adj.pos), wl),
                        _get_x(comp.pos) == _get_x(adj.pos) << wl)
                    zy = z3.Or(_get_y(comp.pos) == z3.LShR(_get_y(adj.pos), wl), 
                        _get_y(comp.pos) == _get_y(adj.pos) << wl)       
                    s.add_soft(zx,str(w))
                    s.add_soft(zy,str(w))
                    w -= 1
        if s.check() != z3.sat:
            if debug_prints:
                print('test is unsat')
            return s

        if debug_prints:
            print('test is sat')

        model_printer(s.model(),comps,fab_dims,wire_lengths)

        #if debug_prints and all(model_checker(s.model(), comps, fab_dims, wire_lengths)):
        #    model_printer(s.model(), comps, fab_dims, wire_lengths)
        #    return (True, s)
        #elif debug_prints:
        #    return (False, s)
        #elif all(model_checker(s.model(), comps, fab_dims, wire_lengths, printer=lambda *x: None)):
        #    return (True, s)
        #else:
        #    return (False, s)
    else: #no provided wire lengths, optimize the manhattan distance
        print('No provided wire lengths. Minimizing total L1 norm')
        constraints, manhattan_dist = place_constraints_opt(comps, fab_dims)
        s = z3.Optimize()
        s.add(constraints)
        h = s.minimize(manhattan_dist)
        s.set('enable_sls', True)
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



def tiny_test(dims=(8,8), debug_prints=True):
    ''' 
        place 4 nodes on a 3x3 fabric [with length 1 wires] 
    '''
    adj = {'n1' : {'n2','n3'}, 'n2' : {'n4'}, 'n3' : {'n4'}, 'n4' : {}}
    run_test(adj, dims, {1}, debug_prints)


def small_test(dims=(8,8), debug_prints=True):
    '''
        place a depth 5 binary tree on a 8 by 8 [with length 2,3 wires] 
    ''' 
    adj = {'n{}'.format(i) : frozenset(('n{}'.format(2*i), 'n{}'.format(2*i+1))) for i in range(1,2**4)}
    run_test(adj, dims, {1,2,3}, debug_prints)


def medium_test(dims=(16,16), debug_prints=True):
    '''
        
    '''
    adj = {'c1' : {'c2','c3'}, 'c2' : {'c4', 'c5'}, 'c3' : {'c6', 'c7'}, 'c4' : {'c8', 'c9'}, 'c5' : {'c10', 'c11'}, 'c6' : {'c12', 'c13'}, 'c7' : {'c14', 'c15'}, 'c8' : {'c16', 'c17'}, 'c9' : {'c18', 'c19'}, 'c10' : {'c20', 'c21'}, 'c11' : {'c22', 'c23'}, 'c12' : {'c24', 'c25'}, 'c13' : {'c26', 'c27'}, 'c14' : {'c28', 'c29'}, 'c15' : {'c30', 'c31'},'n1' : {'n2','n3'}, 'n2' : {'n4', 'n5'}, 'n3' : {'n6', 'n7'}, 'n4' : {'n8', 'n9'}, 'n5' : {'n10', 'n11'}, 'n6' : {'n12', 'n13'}, 'n7' : {'n14', 'n15'}, 'n8' : {'n16', 'n17'}, 'n9' : {'n18', 'n19'}, 'n10' : {'n20', 'n21'}, 'n11' : {'n22', 'n23'}, 'n12' : {'n24', 'n25'}, 'n13' : {'n26', 'n27'}, 'n14' : {'n28', 'n29'}, 'n15' : {'n30', 'n31'}, 'n31' : {'m1'}, 'm1' : {'m2', 'm3', 'm4'}, 'm4' : {'m5'}, 'm5' : {'m6'}, 'm6' : {'m7'}, 'm7' : {'m8'}}
    run_test(adj, dims, {1,2,3}, debug_prints)


def unsat_test(debug_prints=True):
    adj = {'n1' : {'n2','n3','n4','n5','n6'}}
    run_test(adj, (4,4), {1}, debug_prints)

def check_model(model, comps, fab_dims, wire_lengths, printer=print, *pargs, **kwargs):
    correct = [True, True, True]

    mask, mrows, mcols, mwl = _build_standard_mask(fab_dims, wire_lengths)


    #mask formatting functions
    def row_formatter(size, value, idx, v):
        if idx % mcols == mcols - 1:
            return '\n'
        else:
            return ''
    
    spacing = max(len(x.name) for x in comps) + 1

    def choose_between(masks, overlap_c, none_c, w=spacing):
        def elem_f(size, value, idx, v):
            for m,n in masks:
                if m[idx] and not any(other[idx] for other,_ in masks if other is not m):
                    return '{n: ^{w}}'.format(n=n, w=w)
                elif m[idx]:
                    return '{n: ^{w}}'.format(n=overlap_c, w=w)
            return '{n: ^{w}}'.format(n=none_c, w=w)
        return elem_f

    #check correctness of placement
    printer("Checking validity of placement...", *pargs, **kwargs)
    for comp in comps:
        p = zu.Mask(model.evaluate(comp.pos).as_long(), size=mask.size)
        if p.hamming != __COMP_AREA:
            correct[0] = False
            printer('{} has incorrect size, expected {} has {}'.format(comp.name, __COMP_AREA, p.hamming), *pargs, **kwargs)
            printer(p.to_formatted_string(post_f=row_formatter), *pargs, **kwargs)   

        if p & ~mask != 0:
            correct[0] = False
            printer('{} was placed in the masked region'.format(comp.name, p), *pargs, **kwargs)
            elem_f=choose_between([(p,'X'), (mask,'1')], overlap_c='C', none_c = '0')
            printer(p.to_formatted_string(elem_f=elem_f, post_f=row_formatter), *pargs, **kwargs)

    if correct[0]:
        printer("Pass", *pargs, **kwargs)

    #check adjacency is satisfied
    printer("Checking adjacency rules are satisfied...", *pargs, **kwargs)
    for comp in comps:
        p = zu.Mask(model.evaluate(comp.pos).as_long(), size=mask.size)
        for adj in comp.inputs:
            adj_p = zu.Mask(model.evaluate(adj.pos).as_long(), size=mask.size)
            c = []
            for wl in wire_lengths:
                c.extend([p == adj_p << wl,
                    p == adj_p >> wl,
                    p == adj_p << wl*mcols,
                    p == adj_p >> wl*mcols,])

            if not any(c):
                correct[1] = False
                printer('{} and {} are not adjacent'.format(comp.name, adj.name), *pargs, **kwargs)
                elem_f=choose_between([(p,comp.name), (adj_p,adj.name)], overlap_c='X', none_c = '-')
                printer(p.to_formatted_string(elem_f=elem_f, post_f=row_formatter), *pargs, **kwargs)

    if correct[1]:
        printer("Pass", *pargs, **kwargs)

    #check uniqueness of placement
    printer("Checking uniqueness of placement...", *pargs, **kwargs)
    unmarked = set(c for c in comps)
    for comp in comps:
        unmarked.remove(comp)
        p = zu.Mask(model.evaluate(comp.pos).as_long(), size=mask.size)
        for other in unmarked:
            other_p = zu.Mask(model.evaluate(other.pos).as_long(), size=mask.size)
            if p & other_p != 0:
                correct[2] = False
                printer('{} and {} overlap'.format(comp.name, other.name), *pargs, **kwargs)
                elem_f=choose_between([(p,comp.name), (other_p,other.name)], overlap_c='X', none_c = '-')
                printer(p.to_formatted_string(elem_f=elem_f, post_f=row_formatter), *pargs, **kwargs)

    if correct[2]:
        printer("Pass", *pargs, **kwargs)
    
    return correct
