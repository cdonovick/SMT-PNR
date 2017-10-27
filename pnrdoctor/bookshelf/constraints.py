import operator
from collections import defaultdict
from functools import partial, reduce

from .fabric import Fabric
from pnrdoctor.smt import smt_util as su

from pnrdoctor.smt.region import SYMBOLIC, Scalar, Category

def init_regions(one_hot_type, category_type, scalar_type):
    def initializer(region, fabric, design, state, vars, solver):
        constraints = []
        for module in design.modules:
            if module not in vars:
                vars[module] = dict()

            r = state[module]
            for d,p in r.position.items():
                if p is SYMBOLIC:
                    var = scalar_type(module.name + '_' + d.name, solver, d.size)
                    constraints.append(var.invariants)
                elif p is None:
                    continue
                else:
                    var = scalar_type(module.name + '_' + d.name, solver, d.size, p)
                vars[module][d] = var

            for d,c in r.category.items():
                if d.is_one_hot:
                    T = one_hot_type
                else:
                    T = category_type

                if c is SYMBOLIC:
                    var = T(module.name + '_' + d.name, solver, d.size)
                    constraints.append(var.invariants)
                elif c is None:
                    continue
                else:
                    var = T(module.name + '_' + d.name, solver, d.size, c)

                vars[module][d] = var
        return solver.And(constraints)
    return initializer


def pin_resource(region, fabric, design, state, vars, solver):
    constraints = []
    for module in design.modules:
        v = vars[module]
        loc = tuple(v[d] for d in fabric.dims)
        #print(loc)

        cx = []
        for pos in fabric.locations[module.resource]:
            cc = [l == p for l,p in zip(loc, pos)]
            cx.append(solver.And(cc))
        constraints.append(solver.Or(cx))
    return solver.And(constraints)

def HPWL(n_max, g_max):
    return partial(_HPWL, n_max, g_max)

def _HPWL(n_max, g_max, region, fabric, design, state, vars, solver):
    constraints = []
    total = None
    for net in design.nets:
        if not net.is_sig:
            continue
        max = {
            d : reduce(partial(su.max_ite, solver), (vars[t][d].var for t in net.modules)) for d in (fabric.x_dim, fabric.y_dim)
        }

        min = {
            d : reduce(partial(su.min_ite, solver), (vars[t][d].var for t in net.modules)) for d in (fabric.x_dim, fabric.y_dim)
        }

        total_i = None
        for d in max:
            dist = max[d] - min[d]
            if total_i is None:
                total_i = dist
            else:
                total_i  = su.safe_op(operator.add, solver, total_i, dist, pad=1)

        if total_i is not None:
            constraints.append(solver.BVUle(total_i, n_max))
            if total is None:
                total = total_i
            else:
                total = su.safe_op(operator.add, solver, total, total_i, pad=1)

    if total is not None:
        constraints.append(solver.BVUle(total, g_max))

    return solver.And(constraints)
