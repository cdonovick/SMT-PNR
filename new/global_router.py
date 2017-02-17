import monosat as ms
import design
import placer
import pnr2dot
import sys
import os
import time

class PlacedComp:
    def __init__(self, pos, adj=()):
        self.pos = pos
        self.adj = set(adj)
    def dist(self, pc):
        return abs(self.pos[0] - pc.pos[0]) + abs(self.pos[1] - pc.pos[1])


__dist_factor = 2  #takes two monosat edges for every 1 unit of L1 distance
__dist_freedom = 2  #how many extra edges can be used over the L1 distance between components (2 allows for going around other components)


def build_mgraph(fab, placed_comps):
    '''
        Build a MonoSAT graph. Includes every connection box and switch box but only placed components
        Note: For now, there are connection boxes below and to the right of every CLB and a switch box for each CB
              This is not representative of the true fabric -- will be updated later

        Example of coordinate system and naming scheme:

                        (i,j)CLB---(i,j)CBr
                           |          |
                        (i,j)CBb---(i,j)SB

                        r = right
                        b = bottom
                        (i,j) = zero-indexed (x,y) coordinates with origin in top left of fabric
    '''
    g = ms.Graph()
    #add all the placed components to the graph
    fab.populate_CLBs(fab, placed_comps, g)
    #add all internal connection boxes and switch boxes on fabric
    CBr = [[g.addNode('({},{})CB_r'.format(x,y)) for y in range(fab.rows)] for x in range(fab.cols - 1)]
    CBb = [[g.addNode('({},{})CB_b'.format(x,y)) for y in range(fab.rows - 1)] for x in range(fab.cols)]
    SB = [[g.addNode('({},{})SB'.format(x,y)) for y in range(fab.rows-1)] for x in range(fab.cols-1)]
    #add edges
    for y in range(fab.rows):
        for x in range(fab.cols):
            #TODO make less checks (or set up outside of loop)
            if x < fab.cols-1 and y < fab.rows-1:
                g.addUndirectedEdge(CBr[x][y], SB[x][y])
                g.addUndirectedEdge(CBb[x][y], SB[x][y])
            if (x,y) in fab.CLBs:
                if x < fab.cols - 1:
                    g.addUndirectedEdge(fab.CLBs[(x,y)], CBr[x][y])
                if y < fab.rows - 1:
                    g.addUndirectedEdge(fab.CLBs[(x,y)], CBb[x][y])
                if x > 0:
                    g.addUndirectedEdge(CBr[x-1][y], fab.CLBs[(x,y)])
                if y > 0:
                    g.addUndirectedEdge(CBb[x][y-1], fab.CLBs[(x,y)])
            if x > 0 and x <= fab.cols - 1 and y < fab.rows - 1:
                g.addUndirectedEdge(SB[x-1][y], CBb[x][y])
            if y > 0 and x < fab.cols - 1 and y <= fab.rows - 1:
                g.addUndirectedEdge(SB[x][y-1], CBr[x][y])
    fab.populate_edge_dict(g.getEdgeVars())
    return g, CBr, CBb, SB


def comp_dist(pc, adj, model):
    '''
        returns the manhattan distance between two components
    '''
    pcpos = pc.pos.get_coordinates(model)
    adjpos = adj.pos.get_coordinates(model)
    return abs(pcpos[0] - adjpos[0]) + abs(pcpos[1] - adjpos[1])


def total_L1(placed_comps, model):
    '''
    returns the total manhattan distance of placed components
    '''
    dist = 0
    for comp in placed_comps:
        for wire in comp.outputs:
            dist += comp_dist(wire.src, wire.dst, model)
    return dist


def route(fab, des, model, verbose=False):
    '''
        attempt to globally (doesn't consider track widths and allows sharing wires) route all of the placed components
    '''
    g, CBr, CBb, SB = build_mgraph(fab, des.components)
    dist = total_L1(des.components, model)
    print('Placed components have a total L1 distance = ', dist)
    #if made false, still not necessarily unroutable, just unroutable for the given netlist ordering
    successful_routes = []
    heuristic_routable = True
    for pc in des.get_sorted_components(True):
        #keeps track of edges used by this component
        #to allow fanout, only increments edges once for each component
        #TODO: verify electrical correctness
        used_edges = set()
        for wire in pc.outputs_list:
            reaches = g.reaches(fab.getNode(wire.src),fab.getNode(wire.dst))
            dist = __dist_factor*comp_dist(wire.src, wire.dst, model) + __dist_freedom
            dist_constraint = g.distance_leq(fab.getNode(wire.src),fab.getNode(wire.dst), dist)
            c = excl_constraints(wire.src, wire.dst, des.components, fab, g)
            c.append(reaches)
            c.append(dist_constraint)
            sys.stdout = open(os.devnull, 'w')
            result = ms.Solve(ms.And(c))
            sys.stdout = sys.__stdout__

            #performance suffered a lot with small relaxations -- for now trying complete relaxation
            #relax distance constraints if false
            #TODO: come up with better upper bound on distance


            #for now, using one smaller relaxations
            #variable_dist_factor = 2*__dist_factor
            if not result:
                if verbose:
                    print('Not routable with given distance constraint, relaxing distance and trying again')
                del c[-1]
                dist = 2*comp_dist(wire.src, wire.dst, model) + __dist_freedom
                dist_constraint = g.distance_leq(fab.getNode(wire.src),fab.getNode(wire.dst), dist)
                c.append(dist_constraint)
                sys.stdout = open(os.devnull, 'w')
                result = ms.Solve(ms.And(c))
                sys.stdout = sys.__stdout__
            #    variable_dist_factor = 2*variable_dist_factor

            #do a complete relaxation if not routed
            if not result:
                if verbose:
                    print('Not routable with given distance constraint, relaxing distance and trying again')
                del c[-1]
                sys.stdout = open(os.devnull, 'w')
                result = ms.Solve(ms.And(c))
                sys.stdout = sys.__stdout__

            if result:
            #If the result is SAT, you can find the nodes that make up a satisfying path:
                path_node_names = []
                for node in g.getPath(reaches):
                    path_node_names.append(g.names[node])

                if verbose:
                    print("Satisfying path (as a list of nodes): " + str(path_node_names))

                #increment edge counts
                for edge in g.getPath(reaches, return_edge_lits=True):
                    used_edges.add(edge)

                #save path
                successful_routes.append(path_node_names)
            else:
                heuristic_routable = False
                #TODO: if fail to route, need to reorder and possibly re-place
                if verbose:
                    print('Failed to route')
                    print(g.names[fab.getNode(wire.src)])
                    print(g.names[fab.getNode(wire.dst)])
        #increment the edge counts
        for edge in used_edges:
            fab.incrementEdge(edge)

    #generate names
    CBrnames = set()
    for row in CBr:
        for col in row:
            CBrnames.add(g.names[col])
    CBbnames = set()
    for row in CBb:
        for col in row:
            CBbnames.add(g.names[col])
    SBnames = set()
    for row in SB:
        for col in row:
            SBnames.add(g.names[col])

    return heuristic_routable, successful_routes, CBrnames, CBbnames, SBnames


def excl_constraints(src, dest, placed_comps, fab, g):
    '''
        generate the constraints that components other than the source and destination cannot be used in routing
    '''
    c = []
    #don't let it route through other CLBs
    for p in placed_comps:
        if p != src and p != dest:
            c.append(~g.reaches(fab.getNode(src), fab.getNode(p)))
    #don't allow edges that have already reached track capacity
    for edge in fab.getMaxEdges():
        c.append(~edge)
    return c


def test(adj, fab_dims, neighborhood=None):
    '''
       Takes a .dot input, parses using dot2smt, places using smtpnr, and routes
    '''
    frows, fcols = fab_dims
    fab = design.Fabric(dims=fab_dims, W=4)
    p = placer.Placer(fab)
    place_start = time.time()
    if isinstance(adj, str):
        adj = p.parse_file(adj)
    model, d = p.place(adj, neighborhood)
    place_end = time.time()
    place_time = place_end - place_start
    print('It took {} seconds to place'.format(place_time))
    fab.setModel(model)
    route_start = time.time()
    h, routes_nodes, CBr, CBb, SB = route(fab, d, model)
    route_end = time.time()
    route_time = route_end - route_start
    print('It took {} seconds to route'.format(route_time))
    #get all used CLBs
    CLBs = {}
    for comp in d.components:
        pcpos = comp.pos.get_coordinates(model)
        CLBs[pcpos] = '({},{})'.format(pcpos[0], pcpos[1]) + comp.name
    if h:
        pnr2dot.generate_dot((fab.rows, fab.cols), CLBs, CBr, CBb, SB, routes_nodes, 'display.dot')
        return routes_nodes, place_time, route_time
    else:
        print('At least one route failed.')
