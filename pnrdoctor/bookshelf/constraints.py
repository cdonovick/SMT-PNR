import operator
from collections import defaultdict
from functools import partial, reduce

from .fabric import Fabric
from pnrdoctor.smt import smt_util as su

from pnrdoctor.smt.region import SYMBOLIC, Scalar, Category
from pnrdoctor.util import MultiDict


#def do_magic(region, fabric, design, state, vars, solver):
#    #make variables
#    max_x = fabric.max_x
#    max_y = fabric.max_y
#
#    masks = dict()
#    hams = dict()
#    bits = dict()
#    ones = dict()
#
#    for k in design.kinds:
#        bits[k] = w = max_x * max_y * fabric.bounds[k]
#        masks[k] = 0
#        hams[k] = 0
#        ones[k] = solver.TheoryConst(solver.BitVec(w), 1)
#
#
#    constraints = []
#    for module in design.modules:
#        k = module.kind
#        b = bits[k]
#        m = masks[k]
#
#        vars[module] = v = solver.DeclareConst(module.name, solver.BitVec(b))
#        bit_n = solver.DeclareConst(module.name + 'bit_n', solver.BitVec(b))
#
#
#        constraints.append(v == ones[k] << bit_n)
#        constraints.append(solver.BVUlt(bit_n, b))
#        masks[k] = m | v
#        hams[k] += 1
#
#
#    for k,h in hams.items():
#        constraints.append(su.hamming(masks[k] == h))
#
#    return Solver.And(constraints)
#

def do_magic(region, fabric, design, state, vars, solver):
    constraints = []
    ufs = dict()

    mod_id = 0

    for module in design.modules:
        k = module.kind
        vd = vars[module]
        if k not in ufs:
            ufs[k] = solver.DeclareFun(
                k + '_F',
                [vd[fabric.x_dim]._var.sort, vd[fabric.y_dim]._var.sort, vd[fabric.dims[k]]._var.sort],
                solver.BitVec(len(design.modules).bit_length())
            )
        constraints.append(
                ufs[k](vd[fabric.x_dim]._var, vd[fabric.y_dim]._var, vd[fabric.dims[k]]._var) == mod_id
        )
        mod_id += 1


    return solver.And(constraints)

def distinct_pred(region, fabric, design, state, vars, solver):
    constraints = []
    r_v = defaultdict(list)
    concat = solver.Concat

    #Sort of hack to ensure same variable order
    iter_order = dict()
    for m in design.modules:
        v1 = vars[m]
        r = m.resource
        if r not in iter_order:
            iter_order[r] = [d for d in v1.keys()]

        vs = [v1[d].lit for d in iter_order[r]]
        v = reduce(concat, vs)
        r_v[r].append(v)


    for k in r_v:
        if len(r_v[k]) > 1:
            constraints.append(solver.Distinct(r_v[k]))
    return solver.And(constraints)


def init_regions(one_hot_type, category_type, scalar_type):
    def initializer(region, fabric, design, state, vars, solver):
        constraints = []

        #HACK HACK HACK assume each dimension is associated with a single sort
        sorts = dict()

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

                # hack
                if d in sorts:
                    assert sorts[d] == var.lit.sort
                else:
                    sorts[d] = var.lit.sort

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

                # hack
                if d in sorts:
                    assert sorts[d] == var.lit.sort
                else:
                    sorts[d] = var.lit.sort

        # HACK HACK HACK store sorts in region
        region.sorts = sorts
        return solver.And(constraints)
    return initializer


def pin_resource(region, fabric, design, state, vars, solver):
    x_dim, y_dim = fabric.x_dim, fabric.y_dim
    x_sort, y_sort = region.sorts[x_dim], region.sorts[y_dim]
    k_sort = solver.BitVec(len(fabric.kinds).bit_length())

    f = solver.DeclareFun('ResourceUF',
            (x_sort, y_sort, k_sort), k_sort)

    constraints = []

    kind_id_map = dict()
    c = 0
    # BuildUF
    for k in design.kinds:
        print(f'Building for {k}')
        kind_id_map[k] = kid = solver.TheoryConst(k_sort, c)
        for x,y in fabric.locations[k]:
            constraints.append(
                    f(solver.TheoryConst(x_sort, x),
                      solver.TheoryConst(y_sort, y),
                      kid) == kid
                    )
        c += 1

    # assert resource association
    for module in design.modules:
        v = vars[module]
        kid = kind_id_map[module.kind]
        constraints.append(f(v[x_dim].lit, v[y_dim].lit, kid) == kid)


    return solver.And(constraints)

def neihborhood(max_dist):
    return partial(_neihborhood, max_dist)

def _neihborhood(max_dist, region, fabric, design, state, vars, solver):
    constraints = []
    for k,net in enumerate(filter(lambda n : n.is_sig, design.nets)):
        src = net.src
        src_v = vars[src]
        dst_vs = [vars[dst] for dst in net.modules if dst != src]
        for dst_v in dst_vs:
            for d in (fabric.x_dim, fabric.y_dim):
                dist = src_v[d].abs_delta(dst_v[d])
                constraints.append(solver.BVUle(dist, max_dist))

    return solver.And(constraints)


def HPWL(n_max, g_max):
    return partial(_HPWL, n_max, g_max)

def _HPWL(n_max, g_max, region, fabric, design, state, vars, solver):
    constraints = []
    total = None
    l = list(filter(lambda n : n.is_sig, design.nets))

    for net in filter(lambda n : n.is_sig, design.nets):
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
