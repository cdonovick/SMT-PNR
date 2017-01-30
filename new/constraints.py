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


def in_neighborhood(num_hops):
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


