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
        for w in fabric.wire_lengths:
            c.append(z3.And(delta_x == 0, delta_y == w))
            c.append(z3.And(delta_x == w, delta_y == 0)) 

        constraints.append(z3.Or(c))

    return z3.And(constraints)

def nearest_neighbor(components, wires, fabric):
    constraints = []
    for w in wires:
        src = w.src
        dst = w.dst
        for wl in fabric.wire_lengths:
            constraints.append(z3.Or(
                z3.And(src.pos.x == z3.LShR(dst.pos.x, wl) , src.pos.y == dst.pos.y),
                z3.And(src.pos.x == dst.pos.x << wl       , src.pos.y == dst.pos.y),
                z3.And(src.pos.y == z3.LShR(dst.pos.y, wl) , src.pos.x == dst.pos.x), 
                z3.And(src.pos.y == dst.pos.y << wl        , src.pos.x == dst.pos.x)
            ))
    return z3.And(constraints)

def distinct(components, wires, fabric):
    return z3.Distinct(*(c.pos.flat for c in components))
