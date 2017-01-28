'''
Constraint and optimizer functions
'''

import z3
import z3util as zu

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

def distinct(components, wires, fabric):
    return z3.Distinct(*(c.pos.flat for c in components))
