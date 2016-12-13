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
        

def build_graph(adj_dict): 
    '''
        build_graph :: Hash T, repr T => {T->[T]}->{Component}
        adj_dict[x] :: the out edges of x
    '''
    d = dict()

    for x, adj in adj_dict.items():
        if x not in d:
            d[x] = Component(repr(x))

        for y in adj:
            if y not in d:
                d[y] = Component(repr(y))
            d[x].add_output(d[y])
            d[y].add_input(d[x])

    return d.values()


def place_constraints(comps, fab_dims, wire_lengths):
    '''
        place_constraints :: {Component} -> (fabric rows, fabric cols) -> [wire_lengths] -> z3.z3.BoolRef
    '''
    nnode = len(comps)

    #build bit mask
    mwl = max(wire_lengths)
    frows, fcols = fab_dims

    mrows = frows
    mcols = fcols + 2*mwl

    mask = zu.Mask(value=[0]*mwl + [1]*fcols + [0]*mwl, size=mrows*mcols)
    for i in range(mrows.bit_length()):
        mask |= mask << (mcols * 2**i)
    
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
                c.append(z3.Or(comp.pos == adj.pos << wl,
                        comp.pos == adj.pos >> wl,
                        comp.pos == adj.pos >> wl*mcols,
                        comp.pos == adj.pos << wl*mcols,))
            constraints.append(z3.Or(c))

        #constraints.append(comp.pos & mask != 0)
        constraints.append(zu.hamming(comp.pos & mask) == 1)
        constraints.append(comp.pos & imask == 0)

    u = ft.reduce(lambda x,y: x|y, [c.pos for c in comps])
    constraints.append(zu.hamming(u) == nnode)

    return z3.And(constraints)

def check_model(model, comps, fab_dims, wire_lengths):
    return

def print_model(model, comps, fab_dims, wire_lengths):
    p2n = {model.evaluate(x.pos).as_long() : str(x.name).strip("'") for x in comps}

    mwl = max(wire_lengths)
    frows, fcols = fab_dims
    mrows = frows
    mcols = fcols + 2*mwl
    mask = zu.Mask(value=[0]*mwl + [1]*fcols + [0]*mwl, size=mrows*mcols)
    for i in range(mrows.bit_length()):
        mask |= mask << (mcols * 2**i)

    width = 2 + max(len(x) for x in p2n.values())

    s = []
    for i in range(mrows*mcols):
        if mask[i] == 1 and 2**i in p2n:
            s.append('{c: ^{w}}'.format(c=p2n[2**i], w=width))
        elif mask[i] == 1:
            s.append('{c: ^{w}}'.format(c='--', w=width))


        if (i % mcols) == mcols - 1:
            s.append('\n')

    s = ''.join(s)
    print(s)


def run_test(adj, fab_dims, wire_lengths):
    comps = build_graph(adj)
    constraints = place_constraints(comps, fab_dims, wire_lengths)
    s = z3.Solver()
    s.add(constraints)
    if s.check() != z3.sat:
        print('test is unsat')
        return s
    print('test is sat')
    check_model(s.model(), comps, fab_dims, wire_lengths)
    print_model(s.model(), comps, fab_dims, wire_lengths)
    return s

def tiny_test():
    ''' 
        place 4 nodes on a 3x3 fabric with length 1 wires 
    '''
    adj = {'n1' : {'n2','n3'}, 'n2' : {'n4'}, 'n3' : {'n4'}, 'n4' : {}}
    run_test(adj, (3,3), {1})


def small_test():
    '''
        place a depth 5 binary tree on a 6 by 6 with length 2,3 wires 
    ''' 
    adj = {'n{}'.format(i) : frozenset(('n{}'.format(2*i), 'n{}'.format(2*i+1))) for i in range(1,2**4)}
    run_test(adj, (6,6), {2,3})

def unsat_test():
    adj = {'n1' : {'n2','n3','n4','n5','n6'}}
    run_test(adj, (4,4), {1})
