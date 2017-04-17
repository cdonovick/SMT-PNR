'''
Constraint generators
'''

def init_positions(position_type):
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

        return solver.And(constraints)
    return initializer

def assert_pinned(fabric, design, state, vars, solver):
    constraints = []
    for module in design.modules:
        if module in state:
            pos = vars[module]
            constraints.append(pos == pos.encode(state[module][0]))
    return solver.And(constraints)

def distinct(fabric, design, state, vars, solver):
    constraints = []
    for m1 in design.modules:
        for m2 in design.modules:
            if m1 != m2:
                constraints.append(vars[m1].flat != vars[m2].flat)
    return solver.And(constraints)

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
        constraints.append(solver.Or(c))

    return solver.And(constraints)

def pin_IO(fabric, design, state, vars, solver):
    constraints = []
    for module in design.modules:
        if module.op == 'io':
            pos = vars[module]
            c = [pos.x == pos.encode_x(0), 
                 pos.y == pos.encode_y(0)]
            constraints.append(solver.Or(c))
    return solver.And(constraints)



#################################### Routing Constraints ################################

def excl_constraints(fabric, design, p_state, r_state, vars, solver):
    #TODO: For a given module: need to make sure it doesn't reach the wrong port
    c = []
    for m1 in design.modules:
        outputs = {x.dst for x in m1.outputs}
        m1_pos = p_state[m1][0]
        for m2 in design.modules:
            if m2 != m1 and m2 not in outputs:
                m2_pos = p_state[m2][0]
                pe1 = fabric[m1_pos].PE
                pe2 = fabric[m2_pos].PE

                c.append(~solver.g.reaches(vars[pe1.getPort('out')], vars[pe2.getPort('a')]))
                c.append(~solver.g.reaches(vars[pe1.getPort('out')], vars[pe2.getPort('b')]))
                
    return solver.And(c)


def reachability(fabric, design, p_state, r_state, vars, solver):
    reaches = []
    for net in design.nets:
        src_pos = p_state[net.src][0]
        dst_pos = p_state[net.dst][0]
        src_pe = fabric[src_pos].PE
        dst_pe = fabric[dst_pos].PE
        reaches.append(solver.g.reaches(vars[src_pe.getPort(net.src_port)], vars[dst_pe.getPort(net.dst_port)]))
        #make sure not connected to other port
        if net.dst_port == 'a':
            notport = 'b'
        else:
            notport = 'a'
        reaches.append(~solver.g.reaches(vars[src_pe.getPort(net.src_port)], vars[dst_pe.getPort(notport)]))
    return solver.And(reaches)


def multigraph_reachability(fabric, design, p_state, r_state, vars, solver):
    reaches = []
    reaches = []
    for net in design.nets:
        src_pos = p_state[net.src][0]
        dst_pos = p_state[net.dst][0]
        src_pe = fabric[src_pos].PE
        dst_pe = fabric[dst_pos].PE
        reaches.append(vars[net].reaches(vars[src_pe.getPort(net.src_port)], vars[dst_pe.getPort(net.dst_port)]))
    return solver.And(reaches)

def dist_limit(dist_factor):
    if not isinstance(dist_factor, int):
        dist_factor = int(dist_factor) + 1
        print('Received non-integer dist_factor. Need int, so casting to {}'.format(dist_factor))
    def dist_constraints(fabric, design, p_state, r_state, vars, solver):
        constraints = []
        for net in design.nets:
            src_pos = p_state[net.src][0]
            dst_pos = p_state[net.dst][0]
            src_pe = fabric[src_pos].PE
            dst_pe = fabric[dst_pos].PE
            manhattan_dist = int(abs(src_pos[0] - dst_pos[0]) + abs(src_pos[1] - dst_pos[1]))
            #This is just a weird heuristic for now. We have to have at least 2*manhattan_dist because
            #for each jump it needs to go through a port.
            #Additionally, because the way ports are connected (i.e. only accessible from horizontal or vertical tracks)
            #It often happens that a routing is UNSAT for just 2*manhattan_dist so instead we use a factor of 3 and add 1
            #You can adjust it with dist_factor
            constraints.append(vars[net].distance_leq(vars[src_pe.getPort(net.src_port)],
                                                     vars[dst_pe.getPort(net.dst_port)],
                                                     3*dist_factor*manhattan_dist + 1))
        return solver.And(constraints)
    return dist_constraints


def build_msgraph(fabric, design, p_state, r_state, vars, solver):
    # to comply with multigraph, add graph for each net
    # note: in this case, all point to the same graph
    # this allows us to reuse constraints such as dist_limit and use the same model_reader
    for net in design.nets:
        vars[net] = solver.g
    
    #add msnodes for all the used PEs first (because special naming scheme)
    for x in range(fabric.width):
        for y in range(fabric.height):
            if (x, y) in p_state.I:
                vars[fabric[(x, y)].PE.getPort('a')] = solver.g.addNode('({},{})PE_a'.format(x, y))
                vars[fabric[(x, y)].PE.getPort('b')] = solver.g.addNode('({},{})PE_b'.format(x, y))
                vars[fabric[(x, y)].PE.getPort('out')] = solver.g.addNode('({},{})PE_out'.format(x, y))

    for tile in fabric.Tiles.values(): 
        for track in tile.tracks:
            src = track.src
            dst = track.dst
            if src not in vars:
                vars[src] = solver.g.addNode('({},{}){}_i[{}]'.format(str(src.x), str(src.y), src.side.name, str(src.track)))
            if dst not in vars:
                vars[dst] = solver.g.addNode('({},{}){}_i[{}]'.format(str(dst.x), str(dst.y), dst.side.name, str(dst.track)))

            # using r_state to stay consisten with build_net_graphs
            # see that comment
            r_state[track] = solver.g.addEdge(vars[src], vars[dst])

    return solver.And([])


def build_net_graphs(fabric, design, p_state, r_state, vars, solver):
    '''
        An alternative monosat encoding which builds a graph for each net. 
        Handles exclusivity constraints inherently
    '''

    # create graphs for each net
    node_dict = dict()  # used to keep track of nodes in each graph
    for net in design.nets:
        vars[net] = solver.add_graph()
        node_dict[net] = dict()

    # add msnodes for all the used PEs first (because special naming scheme)
    for x in range(fabric.width):
        for y in range(fabric.height):
            if (x, y) in p_state.I:
                for net in design.nets:
                    a = vars[net].addNode('({},{})PE_a'.format(x, y))
                    b = vars[net].addNode('({},{})PE_b'.format(x, y))
                    out = vars[net].addNode('({},{})PE_out'.format(x, y))
                    node_dict[net][a] = solver.false()
                    node_dict[net][b] = solver.false()
                    node_dict[net][out] = solver.false()
                # add each node to vars as well
                # only need to add it once (not for each net/graph)
                vars[fabric[(x, y)].PE.getPort('a')] = a
                vars[fabric[(x, y)].PE.getPort('b')] = b
                vars[fabric[(x, y)].PE.getPort('out')] = out 

    for tile in fabric.Tiles.values(): 
        for track in tile.tracks:
            src = track.src
            dst = track.dst

            if src not in vars:
                for net in design.nets:
                    u = vars[net].addNode('({},{}){}_i[{}]'.format(str(src.x), str(src.y), src.side.name, str(src.track)))
                    node_dict[net][u] = solver.false()
                vars[src] = u
            if dst not in vars:
                for net in design.nets:
                    v = vars[net].addNode('({},{}){}_i[{}]'.format(str(dst.x), str(dst.y), dst.side.name, str(dst.track)))
                    node_dict[net][v] = solver.false()
                vars[dst] = v

            for net in design.nets:
                e = vars[net].addEdge(vars[src], vars[dst])
                node_dict[net][vars[src]] = solver.Or(node_dict[net][vars[src]], e)
                node_dict[net][vars[dst]] = solver.Or(node_dict[net][vars[dst]], e)
                # put in r_state because we need to map track to multiple edges
                # i.e. need BiMultiDict
                # Plus, we only use this in model_reader so it makes sense to have in r_state
                r_state[track] = e

    # now enforce that each node is only used in one of the graphs
    # Note: all graphs have same nodes, so can get them from any graph
    for node in range(0, solver.graphs[0].nodes):
        node_in_graphs = [node_dict[net][node] for net in design.nets]
        solver.AssertAtMostOne(node_in_graphs)

    return solver.And([])
