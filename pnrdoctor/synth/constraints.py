import operator
from collections import defaultdict
from functools import partial, reduce

from .fabric import Fabric
from pnrdoctor.smt import smt_util as su

from pnrdoctor.smt.region import SYMBOLIC, Scalar, Category

def place_model_reader(region, fabric, design, state, vars, solver):
    for module, var_d in vars.items():
        r = state[module]
        pos = {d : v.value for d,v in var_d.items() if d in r.position}
        r.set_position(pos)
        cat = {d : v.value for d,v in var_d.items() if d in r.category}
        r.set_category(cat)


def c2_distinct(fabric, design, state, vars, solver):
    constraints = []
    for m1 in design.modules:
        v1 = vars[m1] 
        for m2 in design.modules:
            if state[m1].parent == state[m2].parent and m1 != m2:
                v1,v2 = vars[m1],vars[m2]
                s = v1.keys() & v2.keys()
                d_it = iter(s)
                d = next(d_it)
                
                b1 = v1[d]._var
                b2 = v2[d]._var

                for d in d_it:
                    b1 = solver.Concat(b1, v1[d]._var)
                    b2 = solver.Concat(b2, v2[d]._var)
         
                constraints.append(b1 != b2)

    return solver.And(constraints)

def n2_distinct(fabric, design, state, vars, solver):
    constraints = []
    for m1 in design.modules:
        v1 = vars[m1] 
        for m2 in design.modules:
            if state[m1].parent == state[m2].parent and m1 != m2:
                v1,v2 = vars[m1],vars[m2]
                s = v1.keys() & v2.keys()
                c = []
                for d in s:
                    c.append(v1[d].distinct(v2[d]))
                constraints.append(solver.Or(c))

    return solver.And(constraints)

def uf_distinct(fabric, design, state, vars, solver):
    constraints = []

    mod_id = 0
    ufs = None

    for module in design.modules:
        vd = vars[module]
        if ufs is None:
            ufs = solver.DeclareFun(
                'distinct', 
                [vd[fabric.x_dim]._var.sort, vd[fabric.y_dim]._var.sort, vd[fabric.z_dim]._var.sort],
                solver.BitVec(len(design.modules).bit_length())
            )

        constraints.append(
                ufs(vd[fabric.x_dim]._var, vd[fabric.y_dim]._var, vd[fabric.z_dim]._var) == mod_id
        )

        mod_id += 1

    return solver.And(constraints)

def do_one_hot(fabric, design, state, vars, solver):
    max_x = fabric.max_x
    max_y = fabric.max_y 
    max_z = fabric.max_z

    bits = max_x * max_y * max_z
    mask = solver.TheoryConst(solver.BitVec(bits), 0)
    one = solver.TheoryConst(solver.BitVec(bits), 1)
    bit_c = solver.TheoryConst(solver.BitVec(bits), bits)
 

    constraints = []
    for module in design.modules:
        vars[module] = v = solver.DeclareConst(module.name, solver.BitVec(bits))
        bit_n = solver.DeclareConst(module.name + 'bit_n', solver.BitVec(bits.bit_length()))
        constraints.append(v == one << bit_n)
        constraints.append(solver.BVUlt(bit_n, bit_c))
        mask = mask | v

    constraints.append(su.hamming(mask) == len(design.modules))    
    return Solver.And(constraints)


def init_regions(one_hot_type, category_type, scalar_type):
    def initializer(fabric, design, state, vars, solver):
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


def HPWL(n_max, g_max):
    return partial(_HPWL, n_max, g_max)

def _HPWL(n_max, g_max, fabric, design, state, vars, solver):
    constraints = []
    total = None
    for net in design.nets:
        max = {
            d : reduce(partial(su.max_ite, solver), (vars[t][d].var for t in net.modules)) for d in fabric.region.scalar_space
        }

        min = {
            d : reduce(partial(su.min_ite, solver), (vars[t][d].var for t in net.modules)) for d in fabric.region.scalar_space
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
