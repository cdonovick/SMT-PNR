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


#################################### Routing Constraints ################################

def excl_constraints(fabric, design, p_state, r_state, vars, solver):
    #TODO: For a given module: need to make sure it doesn't reach the wrong port
    c = []
    for m1 in design.modules:
        outputs = {x.dst for x in m1.outputs}
        m1_pos = p_state[m1]
        for m2 in design.modules:
            if m2 != m1 and m2 not in outputs:
                m2_pos = p_state[m2]
                pe1 = fab[m1_pos].PE
                pe2 = fab[m2_pos].PE

                c.append(~solver.g.reaches(vars[pe1.getPort('out')], vars[pe2.getPort('a')]))
                c.append(~solver.g.reaches(vars[pe1.getPort('out')], vars[pe2.getPort('b')]))
                

    return solver.And(c)


def reachability(fabric, design, p_state, r_state, vars, solver):
    #TODO: Specify port of connection (that would be easier than allowing for either)
    reaches = []
    for m1 in design.modules:
        for port, net in m1.outputs.items():
            src_pos = p_state[net.src]
            dst_pos = p_state[net.dst]
            src_pe = fab[src_pos].PE
            dst_pe = fab[dst_pos].PE
            reaches.append(solver.g.reaches(src_pe.getPort('out'), dst_pe.getPort(port)))
            #make sure not connected to other port
            if port == 'a':
                notport = 'b'
            else:
                notport = 'a'
            reaches.append(~solver.g.reaches(src_pe.getPort('out'), dst_pe.getPort(notport)))
    return solver.And(reaches)


def thing():
    for net in design.nets:
        r_state[net] = (path)

        if track in r_state.I

    if (x, y) in p_sate:
    

def build_msgraph(fabric, design, p_state, r_state, vars, solver):

    #add msnodes for all the used PEs first (because special naming scheme)
    for x in range(fabric.width):
        for y in range(fabric.height):
            if (x, y) in p_state.I:
                vars[fab[(x, y)].PE.getPort('a')] = solver.g.addNode('({},{})PE_a'.format(x, y))
                vars[fab[(x, y)].PE.getPort('b')] = solver.g.addNode('({},{})PE_b'.format(x, y))
                vars[fab[(x, y)].PE.getPort('out')] = solver.g.addNode('({},{})PE_out'.format(x, y))

    for tile in fabric.Tiles.values(): 
        for track in tile.tracks:
            src = track.src
            dst = track.dst
            if src not in vars:
                vars[src] = solver.g.addNode('({},{}){}_i[{}]'.format(str(src.x), str(src.y), src.side.name, str(src.track)))
            if dst not in msnodes:
                vars[dst] = solver.g.addNode('({},{}){}_i[{}]'.format(str(dst.x), str(dst.y), dst.side.name, str(dst.track)))

            vars[track] = solver.g.addEdge(vars[src], vars[dst])


