'''
Constraint generators
'''

def init_positons(position_type):
    '''
    init_positons:
        place initializer
    '''
    def initializer(fabric, design, state, vars, solver):
        constraints = []
        for module in design.modules:
            if module not in vars:
                p = position_type(module.name, fabric)
                vars[module] = p
                constraints.append(p.invariants)

        return solver.And(contraints)
    return initializer

def assert_pinned(position_type):
    def generator(fabric, design, state, vars, solver):
        constraints = []
        for module in design.modules:
            if module in state:
                contraints.append(vars[module] == position_type.encode(state[module]))
        return solver.And(contraints)
    return generator

def distinct(fabric, design, state, vars, solver):
    constaints = []
    for m1 in design.modules:
        for m2 in design.modules:
            if m1 != m2:
                constraints.append(vars[m1].flat != vars[m2].flat)
    return solver.And(contraints)

def nearest_neighbor(fabric, design, state, vars, solver):
    constraints = []
    for net in design.nets:
        src = net.src
        dst = net.dst


        c = []
        dx = vars[src].delta_x_fun(vars[dst])
        dy = vars[src].delta_y_fun(vars[dst])
        c.append(solver.And(dx(0), dy(1)))
        c.append(solver.And(dx(1), dy(0)))
        constaints.append(solver.Or(c))

    return constaints
