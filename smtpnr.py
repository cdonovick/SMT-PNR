import itertools as it
import functools as ft
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

__COMP_SIZE = 1        

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

        constraints.append(zu.hamming(comp.pos) == __COMP_SIZE)
        #The following is insufficient to achieve the previous
        #constraints.append(comp.pos != 0)

        constraints.append(comp.pos & imask == 0)

    u = ft.reduce(lambda x,y: x|y, [c.pos for c in comps])
    constraints.append(zu.hamming(u) == nnode)

    return z3.And(constraints)

def place_constraints_2d(comps, fab_dims, wire_lengths, use_hamming=True):
    '''
        place_constraints :: {Component} -> (int, int) -> [int] -> z3.z3.BoolRef
    '''
    nnode = len(comps)

    frows, fcols = fab_dims

    def _get_x(bv):
        return z3.Extract(frows+fcols-1, frows, bv)

    def _get_y(bv):
        return z3.Extract(frows-1, 0, bv)

    for comp in comps:
        comp.pos = z3.BitVec(comp.name, frows+fcols)

    constraints = []
    for comp in comps:
        for adj in comp.inputs:
            #should dispatch to fabric to get the rules
            c = []
            for wl in wire_lengths:
                #should probably be comp.pos & (shifted adj.pos) != 0,
                #so that components can have variable size
                c.append(z3.Or(
                        _get_x(comp.pos) == z3.LShR(_get_x(adj.pos), wl),
                        _get_x(comp.pos) == _get_x(adj.pos) << wl,
                        _get_y(comp.pos) == z3.LShR(_get_y(adj.pos), wl),
                        _get_y(comp.pos) == _get_y(adj.pos) << wl,
                        ))

            constraints.append(z3.Or(c))

        constraints.append(zu.hamming(comp.pos) == __COMP_SIZE)
        #The following is insufficient to achieve the previous
        #constraints.append(comp.pos != 0)

    if use_hamming:
        d = {c:z3.BitVec(c.name + 'flat', frows*fcols) for c in comps}
        constraints.append(z3.And(
            *(p == _get_x(c.pos) + _get_y(c.pos) * fcols for c,p in d.items())
            ))
        u = ft.reduce(lambda x,y: x|y, d.values())
        constraints.append(zu.hamming(u) == nnode)
    else:
        constraints.append(z3.Distinct(*(c.pos for c in comps)))

    return z3.And(constraints)

def place_constraints_2x(comps, fab_dims, wire_lengths):
    '''
        place_constraints :: {Component} -> (int, int) -> [int] -> z3.z3.BoolRef
    '''
    nnode = len(comps)

    frows, fcols = fab_dims

    for comp in comps:
        comp.pos = (z3.BitVec(comp.name + '_x', frows), z3.BitVec(comp.name + '_y', fcols))


    constraints = []
    for comp in comps:
        for adj in comp.inputs:
            #should dispatch to fabric to get the rules
            c = []
            for wl in wire_lengths:
                #should probably be comp.pos & (shifted adj.pos) != 0,
                #so that components can have variable size
                c.append(z3.Or(
                        z3.And(comp.pos[0] == adj.pos[0], comp.pos[1] == (adj.pos[1] << wl)),
                        z3.And(comp.pos[0] == adj.pos[0], comp.pos[1] == z3.LShR(adj.pos[1], wl)),
                        z3.And(comp.pos[1] == adj.pos[1], comp.pos[0] == (adj.pos[0] << wl)),
                        z3.And(comp.pos[1] == adj.pos[1], comp.pos[0] == z3.LShR(adj.pos[0], wl)),
                        ))

            constraints.append(z3.Or(c))

        constraints.append(zu.hamming(comp.pos[0]) * zu.hamming(comp.pos[1]) == __COMP_SIZE)
        #The following is insufficient to achieve the previous
        #constraints.append(comp.pos != 0)

    #constraints.append(z3.Distinct(*(z3.Concat(c.pos[0], c.pos[1]) for c in comps)))
    d = {c:z3.BitVec(c.name + '_flat', frows*fcols) for c in comps}
    ex = frows*fcols - fcols
    ey = frows*fcols - frows
    for c in comps:
        constraints.append(d[c] == z3.ZeroExt(ex, c.pos[0]) + z3.ZeroExt(ey, c.pos[1]) * fcols)

    u = ft.reduce(lambda x,y: x|y, d.values())
    constraints.append(zu.hamming(u) == nnode)


    return z3.And(constraints)

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
        if p.hamming != __COMP_SIZE:
            correct[0] = False
            printer('{} has incorrect size, expected {} has {}'.format(comp.name, __COMP_SIZE, p.hamming), *pargs, **kwargs)
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
            if (x,y) in p2n:
                s.append('{c: ^{w}}'.format(c=p2n[(x,y)], w=width))
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

def run_test(adj, fab_dims, wire_lengths, debug_prints, 
        constraints_gen=place_constraints,
        model_checker=check_model, 
        model_printer=print_model
        ):

    comps = build_graph(adj)
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

def tiny_test(dims=(3,3), debug_prints=True):
    ''' 
        place 4 nodes on a 3x3 fabric with length 1 wires 
    '''
    adj = {'n1' : {'n2','n3'}, 'n2' : {'n4'}, 'n3' : {'n4'}, 'n4' : {}}
    run_test(adj, dims, {1}, debug_prints)


def small_test(dims=(6,6), debug_prints=True):
    '''
        place a depth 5 binary tree on a 6 by 6 with length 2,3 wires 
    ''' 
    adj = {'n{}'.format(i) : frozenset(('n{}'.format(2*i), 'n{}'.format(2*i+1))) for i in range(1,2**4)}
    run_test(adj, dims, {2,3}, debug_prints)

def unsat_test(debug_prints=True):
    adj = {'n1' : {'n2','n3','n4','n5','n6'}}
    run_test(adj, (4,4), {1}, debug_prints)
