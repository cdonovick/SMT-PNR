'''
Constraint and optimizer functions
'''

import z3
import z3util as zu
import math

def nearest_neighbor_var(components, wires, fabric):
    constraints = []
    for w in wires:
        src = w.src
        dst = w.dst

        cx, delta_x = src.pos.delta_x(dst.pos)
        cy, delta_y = src.pos.delta_y(dst.pos)
        
        constraints.append(cx)
        constraints.append(cy)

        c = []
        for wl in fabric.wire_lengths:
            c.append(z3.And(delta_x == 0 , delta_y == wl))
            c.append(z3.And(delta_x == wl, delta_y == 0 )) 

        constraints.append(z3.Or(c))

    return z3.And(constraints)

def nearest_neighbor_fast(components, wires, fabric):
    constraints = []
    for w in wires:
        src = w.src
        dst = w.dst
        
        c = []
        dx = src.pos.delta_x_fun(dst.pos)
        dy = src.pos.delta_y_fun(dst.pos)

        for wl in fabric.wire_lengths:
            c.append(z3.And(dx(0) , dy(wl)))
            c.append(z3.And(dx(wl), dy(0)))

        constraints.append(z3.Or(c))
    return z3.And(constraints)


def min_L1(components, wires, fabric):
    #TODO change to num_conns*(fabric.rows + fabric.cols)
    n = fabric.rows + fabric.cols
    #create functions for zero-extension (or lack thereof)
    if n > fabric.cols:
        def zext_x(bv):
            return z3.ZeroExt(n, bv)
    elif fabric.rows > fabric.cols:
        def zext_x(bv):
            return z3.ZeroExt(fabric.rows-fabric.cols, bv)
    else:
        def zext_x(bv):
            return bv

    if n > fabric.rows:
        def zext_y(bv):
            return z3.ZeroExt(n, bv)
    elif fabric.cols > fabric.rows:
        def zext_y(bv):
            return z3.ZeroExt(fabric.cols - fabric.rows, bv)
    else:
        def zext_y(bv):
            return bv

    manhattan_dist = 0
    for w in wires:
        src = w.src
        dst = w.dst

        #cx, dx = src.pos.delta_x(dst.pos)
        #cy, dy = src.pos.delta_y(dst.pos)
        manhattan_dist += zu.absolute_value(zext_x(src.pos.x) - zext_x(dst.pos.x)) + zu.absolute_value(zext_y(src.pos.y) - zext_y(dst.pos.y))
    return [], z3.simplify(manhattan_dist)


def in_neighborhood(num_hops):
    '''
    in_neighborhood(1) should equal nearest_neighbor_fast
    '''

    if num_hops < 1:
        raise ValueError('num_hops must be >= 1, recieved {}'.format(num_hops))

    def _get_pairs(wire_lengths, n):
        if n == 1:
            s = set()
            for wl in wire_lengths:
                s.add((0, wl))
                s.add((wl, 0))
        elif n > 1:
            s = _get_pairs(wire_lengths, n-1)
            s2 = set()
            for p in s:
                for wl in wire_lengths:
                    s2.add((p[0], p[1]+wl))
                    s2.add((p[0]+wl, p[1]))
            s = s.union(s2)
        else:
            raise ValueError('n must be >= 1, recieved {}'.format(n))
        return s

    def neighborhood(components, wires, fabric):
        distances = _get_pairs(fabric.wire_lengths, num_hops)
        constraints = []
        for w in wires:
            src = w.src
            dst = w.dst

            delta_x = src.pos.delta_x_fun(dst.pos)
            delta_y = src.pos.delta_y_fun(dst.pos)
            
            c = []
            for dx, dy in distances:
                c.append(z3.And(delta_x(dx), delta_y(dy)))

            constraints.append(z3.Or(c))
        return z3.And(constraints)
    return neighborhood



def distinct(components, wires, fabric):
    return z3.Distinct(*(c.pos.flat for c in components))


def opt_distinct(components, wires, fabric):
    ''' Distinct for Optimizer -- because needs to be simplified for z3.Optimize()'''
    return z3.simplify(z3.Distinct(*(c.pos.flat for c in components)), ':blast-distinct', True)

