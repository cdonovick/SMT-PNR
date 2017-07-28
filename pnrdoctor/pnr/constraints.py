'''
Constraint generators
'''
from functools import partial
import itertools
import random
import string

from pnrdoctor.design.module import Resource
from pnrdoctor.fabric.fabricutils import trackindex
from pnrdoctor.util import STAR

from .pnrutils import get_muxindex, get_muxindices


def init_positions(position_type):
    '''
    init_positons:
        place initializer
    '''
    def initializer(fabric, design, state, vars, solver):
        constraints = []
        for module in design.physical_modules:
            if module not in vars:
                p = position_type(module.name, fabric)
                vars[module] = p
                constraints.append(p.invariants)
        return solver.And(constraints)
    return initializer


def init_random(position_type):
    def initializer(fabric, design, state, vars, solver):
        constraints = []
        # random.shuffle shuffles in place and needs indexable data type
        physical_modules = list(design.physical_modules)
        random.shuffle(physical_modules)
        for module in physical_modules:
            if module not in vars:
                randstring = ''
                for s in random.sample(string.ascii_letters + string.digits, 5):
                    randstring += s
                p = position_type(module.name + randstring, fabric)
                vars[module] = p
                constraints.append(p.invariants)
        return solver.And(constraints)
    return initializer


def assert_pinned(fabric, design, state, vars, solver):
    constraints = []
    for module in design.physical_modules:
        if module in state:
            pos = vars[module]
            constraints.append(pos == pos.encode(state[module][0]))
    return solver.And(constraints)

def pin_reg(reg, p):
    def _pin_reg(fabric, design, state, vars, solver):
        pos = vars[reg]
        return solver.And(pos.x == pos.encode_x(p[0]), pos.y == pos.encode_y(p[1]))

    return _pin_reg

def distinct(fabric, design, state, vars, solver):
    constraints = []
    for m1 in design.physical_modules:
        for m2 in design.physical_modules:
            if m1 != m2 and m1.resource == m2.resource:
                v1,v2 = vars[m1],vars[m2]
                c = v1.flat != v2.flat

                if m1.resource == Resource.Reg:
                    constraints.append(solver.Or(c,  v1.c != v2.c))
                else:
                    constraints.append(c)

    return solver.And(constraints)

def register_colors(fabric, design, state, vars, solver):
    constraints = []
    for tie in design.physical_ties:
        src = tie.src
        dst = tie.dst
        if src.resource == dst.resource == Resource.Reg:
            constraints.append(vars[src].c == vars[dst].c)
    return solver.And(constraints)

def nearest_neighbor(fabric, design, state, vars, solver):
    dxdy = ((0,1), (1,0))
    return _neighborhood(dxdy, fabric, design, state, vars, solver)


def neighborhood(dist):
    dxdy = set((x,y) for x,y in itertools.product(range(dist+1), repeat=2) if x+y <= dist and x+y > 0)
    return partial(_neighborhood, dxdy)

def _neighborhood(dxdy, fabric, design, state, vars, solver):
        constraints = []
        for tie in design.physical_ties:
            src = tie.src
            dst = tie.dst
            c = []
            dx = vars[src].delta_x_fun(vars[dst])
            dy = vars[src].delta_y_fun(vars[dst])
            #c.append(solver.And(dx(0), dy(0)))
            for x, y in dxdy:
                c.append(solver.And(dx(x), dy(y)))
            constraints.append(solver.Or(c))


        return solver.And(constraints)


def pin_IO(fabric, design, state, vars, solver):
    constraints = []
    for module in design.modules_with_attr_val('type_', 'IO'):
        pos = vars[module]
        c = [pos.x == pos.encode_x(0),
             pos.y == pos.encode_y(0)]
        constraints.append(solver.Or(c))
    return solver.And(constraints)


def pin_resource(fabric, design, state, vars, solver):
    constraints = []
    for module in design.physical_modules:
        pos = vars[module]
        c = []
        for p in fabric.locations[module.resource]:
            if len(p) > 3 or len(p) < 2:
                raise NotImplementedError("Can't haldle dimension other than 2 / 3")

            cc = [pos.x == pos.encode_x(p[0]), pos.y == pos.encode_y(p[1])]
            if len(p) == 3:
                cc.append(pos.c == pos.encode_c(p[2]))
            c.append(solver.And(cc))

        constraints.append(solver.Or(c))
    return solver.And(constraints)


#################################### Routing Constraints ################################

def excl_constraints(fabric, design, p_state, r_state, vars, solver, layer=16):
    '''
        Exclusivity constraints for single graph encoding
        Works with build_msgraph, reachability and dist_limit
    '''
    c = []
    # Note: exclusivity constraints only used for single graph encoding
    # i.e. don't need to retrieve graph as graph = vars[net]
    # this is because exclusivity constraints are handled implicitly by the
    # multigraph encoding
    graph = solver.graphs[0]

    # for connected modules, make sure it's not connected to wrong inputs
    # TODO: Fix this so doesn't assume only connected to one input port
    # there might be weird cases where you want to drive multiple inputs
    # of dst module with one output
    for tie in design.physical_ties:
        # hacky don't handle wrong layer here
        # and if destination is a register, it only has one port
        # so it doesn't need exclusivity constraints
        if tie.width != layer or tie.dst.resource == Resource.Reg:
            continue

        src = tie.src
        dst = tie.dst

        src_index = get_muxindex(src, p_state, layer, tie.src_port)

        # get all the destination ports that connect these two modules
        s = set([n.dst_port for n in dst.inputs.values()
                 if n.src == src and n.src_port == tie.src_port])

        for port in fabric.port_names[(dst.resource, layer)].sinks - s:
            dst_index = get_muxindex(dst, p_state, layer, port)
            c.append(~graph.reaches(vars[fabric[src_index].source],
                                    vars[fabric[dst_index].sink]))

    # make sure modules that aren't connected are not connected
    for mdst in design.physical_modules:
        # get contracted inputs
        # TODO: test for correctness
#        contracted_inputs = mdst.inputs.values() & design.physical_ties
        inputs = {x.src for x in mdst.inputs.values()}
        contracted_inputs = set()
        for src in inputs:
            if src.resource == Resource.Fused:
                assert len(src.inputs) <= 1
                if src.inputs:
                    srctie = next(iter(src.inputs.values()))
                    src = srctie.src
                else:
                    continue
            # add the (potentially contracted) src
            contracted_inputs.add(src)

        for msrc in design.physical_modules:
            if msrc != mdst and msrc not in contracted_inputs:
                # iterate through all port combinations for m2-->m1 connections
                for src_port, dst_port \
                    in itertools.product(fabric.port_names[(msrc.resource, layer)].sources,
                                         fabric.port_names[(mdst.resource, layer)].sinks):

                    dst_index = get_muxindex(mdst, p_state, layer, dst_port)
                    src_index = get_muxindex(msrc, p_state, layer, src_port)

                    # assert that these modules' ports do not connect
                    c.append(~graph.reaches(vars[fabric[src_index].source],
                                            vars[fabric[dst_index].sink]))

    return solver.And(c)


def reachability(fabric, design, p_state, r_state, vars, solver, layer=16):
    '''
        Enforce reachability for ties in single graph encoding
        Works with build_msgraph, excl_constraints and dist_limit
    '''
    reaches = []
    for net in design.physical_nets:
        graph = vars[net]
        # hacky don't handle wrong layer
        if net.width != layer:
            continue

        for tie in net.ties:

            src_index, dst_index = get_muxindices(tie, p_state)

            reaches.append(graph.reaches(vars[fabric[src_index].source],
                                         vars[fabric[dst_index].sink]))

    return solver.And(reaches)


# TODO: Fix indexing for distance constraints
def dist_limit(dist_factor, include_reg=False):
    '''
       Enforce a global distance constraint. Works with single or multi graph encoding
       dist_factor is intepreted as manhattan distance on a placement grid
       (i.e. distance between adjacent PEs is 1)
    '''
    if not isinstance(dist_factor, int):
        raise ValueError('Expected integer distance factor. Received {}'.format(type(dist_factor)))

    def dist_constraints(fabric, design, p_state, r_state, vars, solver, layer=16):
        constraints = []
            for tie in net.ties:

                src = tie.src
                dst = tie.dst

                src_index = get_muxindex(src, p_state, layer, tie.src_port)
                dst_index = get_muxindex(dst, p_state, layer, tie.dst_port)

                src_pos = p_state[src][0]
                dst_pos = p_state[dst][0]

                manhattan_dist = int(abs(src_pos[0] - dst_pos[0]) + abs(src_pos[1] - dst_pos[1]))

                # not imposing distance constraints for reg-->reg ties -- because sometimes needs to take weird path
                if dst.resource != Resource.Reg:
                    # This is just a weird heuristic for now. We have to have at least 2*manhattan_dist because
                    # for each jump it needs to go through a port. So 1 in manhattan distance is 2 in monosat distance
                    # Additionally, because the way ports are connected (i.e. only accessible from horizontal or vertical tracks)
                    # It often happens that a routing is UNSAT for just 2*manhattan_dist so instead we use a factor of 3 and add 1
                    # You can adjust it with dist_factor
                    heuristic_dist = 3*dist_factor*manhattan_dist + 1
                    constraints.append(graph.distance_leq(vars[fabric[src_index].source],
                                                              vars[fabric[dst_index].sink],
                                                              heuristic_dist))
                elif include_reg:
                    reg_heuristic_dist = 4*dist_factor*manhattan_dist + 1
                    constraints.append(graph.distance_leq(vars[fabric[src_index].source],
                                                              vars[fabric[dst_index].sink],
                                                              reg_heuristic_dist))

        return solver.And(constraints)
    return dist_constraints


# TODO: Fix node generation. --might be fine already?
def build_msgraph(fabric, design, p_state, r_state, vars, solver, layer=16):
    # to comply with multigraph, add graph for each tie
    # note: in this case, all point to the same graph
    # this allows us to reuse constraints such as dist_limit and use the same model_reader
    solver.add_graph()
    for net in design.physical_nets:
        # hacky don't make graph for different layer nets
        if net.width != layer:
            continue
        vars[net] = solver.graphs[0]

    graph = solver.graphs[0]  # only one graph in this encoding

    # add nodes for modules
    for mod in design.physical_modules:
        for _type in {'sources', 'sinks'}:
            for port_name in getattr(fabric.port_names[(mod.resource, layer)], _type):
                index = get_muxindex(mod, p_state, layer, port_name)
                p = getattr(fabric[index], _type[:-1])  # source/sink instead of sources/sinks
                vars[p] = graph.addNode(p.name)

    pindex = pathindex(src=STAR, snk=STAR, bw=layer)
    for track in fabric[pindex]:
        src = track.src
        dst = track.dst
        # naming scheme is (x, y)Side_direction[track]
        # checking port resources
        # don't make nodes for PEs/Mem that don't have anything placed there
        if src.resource in {Resource.PE, Resource.Mem} and (src.x, src.y) not in p_state.I:
            continue
        if src not in vars:
            vars[src] = graph.addNode(src.name)
        if dst not in vars:
            vars[dst] = graph.addNode(dst.name)

        # create a monosat edge
        e = graph.addEdge(vars[src], vars[dst])
        vars[e] = track  # we need to recover the track in model_reader

    return solver.And([])


def build_net_graphs(fabric, design, p_state, r_state, vars, solver, layer=16):
    '''
        An alternative monosat encoding which builds a graph for each tie.
        Handles exclusivity constraints inherently
    '''

    # NOTE: Currently broken for fanout
    # Making ties contain whole tree of connections will fix this issue

    # NOTE 2: Also broken by new unplaceable module changes. Nets don't
    # correspond to layers any more (or at least until the ties are the whole tree)

    # create graphs for each tie
    node_dict = dict()  # used to keep track of nodes in each graph
    for net in design.physical_nets:
        vars[net] = solver.add_graph()
        node_dict[net] = dict()

    sources = fabric[layer].sources
    sinks = fabric[layer].sinks

    # add nodes for modules to each graph
    for mod in design.physical_modules:
        for _type in {'sources', 'sinks'}:
            for port_name in getattr(fabric.port_names[(mod.resource, layer)], _type):
                index = get_muxindex(mod, p_state, layer, port_name)
                p = getattr(fabric[index], _type[:-1]) # source/sink instead of sources/sinks
                # add to each graph
                for net in design.physical_nets:
                    graph = vars[net]
                    n = graph.addNode(p.name)
                    # these will be overwritten each time, but that's fine
                    # nodes are just ints, so we just need the int representing
                    # that port
                    vars[p] = n
                    vars[(mod, port_name)] = n
                    node_dict[net][n] = solver.false()  # for layer assertions


    pindex = pathindex(src=STAR, snk=STAR, bw=layer)
    for track in fabric[pindex]:
        src = track.src
        dst = track.dst

        # if port does not have a node yet, add one for each net
        # and keep track of them in vars
        if src not in vars:
            for net in design.physical_nets:
                u = vars[net].addNode(src.name)
                node_dict[net][u] = solver.false()
            vars[src] = u
        if dst not in vars:
            for net in design.physical_nets:
                v = vars[net].addNode(dst.name)
                node_dict[net][v] = solver.false()
            vars[dst] = v

        # keep track of whether a node is 'active' based on connected edges
        for net in design.physical_nets:
            e = vars[net].addEdge(vars[src], vars[dst])
            node_dict[net][vars[src]] = solver.Or(node_dict[net][vars[src]], e)
            node_dict[net][vars[dst]] = solver.Or(node_dict[net][vars[dst]], e)
            # put in r_state because we need to map track to multiple edges
            # i.e. need BiMultiDict
            # Plus, we only use this in model_reader so it makes sense to have in r_state
            vars[e] = track

    # now enforce that each node is only used in one of the graphs
    # Note: all graphs have same nodes, so can get them from any graph
    for node in range(0, solver.graphs[0].nodes):
        node_in_graphs = [node_dict[net][node] for net in design.physical_nets]
        solver.AssertAtMostOne(node_in_graphs)

    return solver.And([])
