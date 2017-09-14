import itertools
from pnrdoctor.design.module import Resource
from pnrdoctor.smt.region import SYMBOLIC, Scalar, Category


def ilp_init_regions(category_type, scalar_type):

    def ilp_initializer(region, fabric, design, state, vars, solver):
        constraints = []
        for module in design.modules:
            if module not in vars:
                vars[module] = dict()

            r = state[module]
            for d, p in r.position.items():
                if p is SYMBOLIC:
                    var = scalar_type(module.name + '_' + d.name, solver, d.size)
                    constraints += var.invariants
                elif p is None:
                    continue
                else:
                    var = scalar_type(module.name + '_' + d.name, solver, d.size, p)

                vars[module][d] = var

            for d, c in r.category.items():
                if d == fabric.tracks_dim and module.resource != Resource.Reg:
                    continue
                if c is SYMBOLIC:
                    var = category_type(module.name + '_' + d.name, solver, d.size)
                    constraints += var.invariants
                elif c is None:
                    continue
                else:
                    var = scalar_type(module.name + '_' + d.name, solver, d.size, c)

                vars[module][d] = var                
                
        return constraints

    return ilp_initializer


def ilp_distinct(region, fabric, design, state, vars, solver):
    M = fabric.cols*fabric.rows

    c = []

    for m1, m2 in itertools.combinations(list(design.modules), 2):
        pos1, pos2 = vars[m1], vars[m2]

        r1, c1 = pos1[fabric.rows_dim], pos1[fabric.cols_dim]
        r2, c2 = pos2[fabric.rows_dim], pos2[fabric.cols_dim]

        if m1.resource == m2.resource:
            p = solver.addBinVar()
            q = solver. addBinVar()
            c.append(c1.var + 1 <= c2.var + M*(p + q))
            c.append(r1.var + 1 <= r2.var + M*(1 + p - q))
            c.append(c1.var - 1 >= c2.var - M*(1 - p + q))
            c.append(r1.var - 1 >= r2.var - M*(2 - p - q))

    return c


def ilp_neighborhood(dist):

    def _ilp_neighborhood(region, fabric, design, state, vars, solver):
        constraints = []

        for tie in design.ties:
            pos1 = vars[tie.src]
            pos2 = vars[tie.dst]

            r1, c1 = pos1[fabric.rows_dim], pos1[fabric.cols_dim]
            r2, c2 = pos2[fabric.rows_dim], pos2[fabric.cols_dim]

            # enumerate constraints for L1 norm (all must be satisfied)
            constraints.append(c1.var - c2.var + r1.var - r2.var <= dist)
            constraints.append(c1.var - c2.var + r2.var - r1.var <= dist)
            constraints.append(c2.var - c1.var + r1.var - r2.var <= dist)
            constraints.append(c2.var - c1.var + r2.var - r1.var <= dist)

        return constraints

    return _ilp_neighborhood


def ilp_pin_resource_disj(region, fabric, design, state, vars, solver):
    '''
    Associate one binary variable with each possible location of a module
    '''
    M = fabric.cols*fabric.rows

    constraints = []

    for module in design.modules:
        pos = vars[module]
        r, c = pos[fabric.rows_dim], pos[fabric.cols_dim]
        bool_vars = []

        for p in fabric.locations[module.resource]:
            if len(p) > 3 or len(p) < 2:
                raise NotImplementedError("Can't handle dimension other than 2 or 3")

            b = solver.addBinVar()
            bool_vars.append(b)

            constraints.append(c.var <= pos.encode_x(p[0]) + (1-b)*M)
            constraints.append(c.var >= pos.encode_x(p[0]) - (1-b)*M)
            constraints.append(r.var <= pos.encode_y(p[1]) + (1-b)*M)
            constraints.append(r.var >= pos.encode_y(p[1]) - (1-b)*M)

        constraints.append(solver.quicksum(bool_vars) >= 1)

    return constraints


def ilp_pin_resource_structured(region, fabric, design, state, vars, solver):

    M = fabric.cols*fabric.rows

    constraints = []
    for module in design.modules:
        pos = vars[module]
        r, c = pos[fabric.rows_dim], pos[fabric.cols_dim]
        if module.resource == Resource.Mem:
            bool_vars_col = []
            for col in fabric.resdimvals(Resource.Mem, fabric.cols_dim):
                b = solver.addBinVar()
                bool_vars_col.append(b)
                constraints.append(c.var <= col + (1-b)*M)
                constraints.append(c.var >= col - (1-b)*M)

            # only one can be true -- almost a SOS1 constraint but not quite...
            constraints.append(solver.quicksum(bool_vars_col) == 1)

            bool_vars_row = []
            for row in fabric.resdimvals(Resource.Mem, fabric.rows_dim):
                b = solver.addBinVar()
                bool_vars_row.append(b)
                constraints.append(r.var <= row + (1-b)*M)
                constraints.append(r.var >= row - (1-b)*M)

            # only one can be true
            constraints.append(solver.quicksum(bool_vars_row) == 1)

        elif module.resource == Resource.Reg:
            bool_vars = []

            for col in fabric.resdimvals(Resource.Reg, fabric.cols_dim):
                b = solver.addBinVar()
                bool_vars.append(b)
                constraints.append(c.var <= col + (1-b)*M)
                constraints.append(c.var >= col - (1-b)*M)

            # only one can be true
            constraints.append(solver.quicksum(bool_vars) == 1)

        else:
            # Not placed in a memory column
            # TODO: Figure out if there's a better encoding
            # there may be a way that avoids redundancy
            for col in fabric.resdimvals(Resource.Mem, fabric.cols_dim):
                b = solver.addBinVar()
                constraints.append(c.var <= col - 1 + b*M)
                constraints.append(c.var >= col + 1 - (1-b)*M)

    return constraints


ilp_pin_resource = ilp_pin_resource_structured


def ilp_pin_IO(region, fabric, design, state, vars, solver):
    M = fabric.cols*fabric.rows

    constraints = []

    for module in design.modules_with_attr_val('type_', 'IO'):
        pos = vars[module]
        r, c = pos[fabric.rows_dim], pos[fabric.cols_dim]
        b1 = solver.addBinVar()
        b2 = solver.addBinVar()
        constraints.append(0 >= c.var - (1-b1)*M)
        constraints.append(0 >= r.var - (1-b2)*M)
        constraints.append(b1 + b2 >= 1)

    return constraints


def ilp_register_colors(region, fabric, design, state, vars, solver):
    constraints = []

    for tie in design.ties:
        src = tie.src
        dst = tie.dst
        if src.resource == dst.resource == Resource.Reg:
            constraints.append(vars[src][fabric.tracks_dim].var == vars[dst][fabric.tracks_dim].var)

        return constraints
