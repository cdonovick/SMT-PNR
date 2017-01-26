'''
Constraint and optimizer functions
'''

import z3
import z3util as zu

def nearest_neighbor(components, wires, fabric):
    constraints = []
    for w in wires:
        src = s.src
        dst = s.dst

        cx, delta_x = src.pos.delta_x(dst.pos)
        cy, delta_y = src.pos.delta_y(dst.pos)
        
        contraints.append(cx)
        contraints.append(cy)

        c = []
        for w in fabric.wire_lengths:
            c.append(z3.And(delta_x == 0, delta_y == w))
            c.append(z3.And(delta_x == w, delta_y == 0)) 

        contraints.append(z3.Or(c))

    return z3.And(contraints)

def distinct(components, wires, fabric):
    return z3.Distinct(*(c.pos.flat for c in components))




