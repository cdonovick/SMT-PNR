from .fabric import Fabric


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


def pin_resource_structured(region, fabric, design, state, vars, solver):
    R = Fabric.Resource
    constraints = []
    
    for module in design.modules:
        v = vars[module]
        r,c,l = v[fabric.rows_dim], v[fabric.cols_dim], v[fabric.luts_dim]
            
        # no corners
        c = solver.And([
            solver.Or([r != 0,             c !=0]),
            solver.Or([r != 0,             c != fabric.cols-1]),
            solver.Or([r != fabric.rows-1, c != 0]),
            solver.Or([r != fabric.rows-1, c != fabric.cols-1]),
        ])
        constraints.append(c)

        res = module.resource
        if res in (R.IO, R.Logic):
            c_io = [
                solver.Or([r == 0, r == fabric.rows-1]),
                solver.Or([c == 0, c == fabric.cols-1]),
            ]
            if res == R.IO:
                c_io.append(solver.Or([l == 0, l == 1]))
            c_io = solver.And(c_io)

        else:
            c_io = True

        if res in (R.Mem, R.Logic) :
            c_mem = [solver.Or([c == 3, c == 10])]
            if res == R.Mem:
                c_mem.append(l == 0)
                c_mem.append(solver.Extract(r.var, 0, 0) == 0)
            c_mem = solver.And(c_mem)
        else:
            c_mem = True

        if res == R.Logic:
            c = solver.And([
                solver.Not(c_io),
                solver.Not(c_mem),
            ])
        else:
            c = solver.And([
                c_io,
                c_mem,
            ])
        
        constraint.append(c)
    return solver.And(constriants)


