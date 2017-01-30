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

def distinct(components, wires, fabric):
    return z3.Distinct(*(c.pos.flat for c in components))

def opt_distinct(components, wires, fabric):
    ''' Distinct for Optimizer -- because needs to be simplified for z3.Optimize()'''
    return z3.simplify(z3.Distinct(*(c.pos.flat for c in components)), ':blast-distinct', True)
