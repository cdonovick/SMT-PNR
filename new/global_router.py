import monosat as ms
import design
import placer

class MFabric:
    def __init__(self, fab_dims, model, W):
        #For now, W is universal number of tracks (assumed same for every edge)
        self.rows = fab_dims[0]
        self.cols = fab_dims[1]
        self.CLBs = {}
        self._edge_dict = {}
        self.model = model
        self.W = W
        
    def getNode(self, pc):
        return self.CLBs[pc.pos.get_coordinates( self.model)] #return the monosat node associated with that component

    def populate_edge_dict(self, edges):
        #add all the edges to the edge dictionary (an undirected edge is represented by two directed edges)
        for e in edges:
            self._edge_dict[e.lit] = (0, e)

    def incrementEdge(self, e):
        #increments edge count
        if e.lit in self._edge_dict:
            t = self._edge_dict[e.lit]
            self._edge_dict[e.lit] = (t[0]+1, t[1])
        else:
            raise ValueError('Edge {} does not yet exist in the graph'.format(e))

    def getEdgeCount(self, e):
        return self._edge_dict[e.lit][0]

    def getMaxEdges(self):
        #returns a list of the edges which are at capacity
        #TODO maybe implement a heap-type structure eventually -- but accessing by edges is also convenient...
        max_edges = []
        for e_lit, t in self._edge_dict.items():
            count = t[0]
            edge = t[1]
            if count >= self.W:
                max_edges.append(edge)
        return max_edges
    
    def populate_CLBs(self, fab, placed_comps, g):
        '''
        add placed components to the fabric
        '''
        for pc in placed_comps:
            pcpos = pc.pos.get_coordinates(self.model)
            fab.CLBs[pcpos] = g.addNode('{}({},{})'.format(pc.name,pcpos[0],pcpos[1])) 
    

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

                        CLB(i,j)---CB(i,j)r
                           |          |
                        CB(i,j)b---SB(i,j)

                        r = right
                        b = bottom
                        (i,j) = zero-indexed (x,y) coordinates with origin in top left of fabric
    '''
    g = ms.Graph()
    #add all the placed components to the graph
    fab.populate_CLBs(fab, placed_comps, g)
    #add all internal connection boxes and switch boxes on fabric
    CBr = [[g.addNode('CB({},{})_r'.format(x,y)) for y in range(fab.rows)] for x in range(fab.cols - 1)]
    CBb = [[g.addNode('CB({},{})_b'.format(x,y)) for y in range(fab.rows - 1)] for x in range(fab.cols)]
    SB = [[g.addNode('SB({},{})'.format(x,y)) for y in range(fab.rows-1)] for x in range(fab.cols-1)]
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
    return g


def comp_dist(pc, adj, model):
    '''
        returns the manhattan distance between two components
    '''
    pcpos = pc.pos.get_coordinates(model)
    adjpos = adj.pos.get_coordinates(model)
    return abs(pcpos[0] - adjpos[0]) + abs(pcpos[1] - adjpos[1])


def route(fab, des, model, W, verbose = False):
    '''
        attempt to globally (doesn't consider track widths and allows sharing wires) route all of the placed components
    '''
    g = build_mgraph(fab, des.components)
    #if made false, still not necessarily unroutable, just unroutable for the given netlist ordering
    heuristic_routable = True
    for pc in des.components:
        for wire in pc.outputs:
            reaches = g.reaches(fab.getNode(wire.src),fab.getNode(wire.dst))
            dist = __dist_factor*comp_dist(wire.src, wire.dst, model) + __dist_freedom
            dist_constraint = g.distance_leq(fab.getNode(wire.src),fab.getNode(wire.dst), dist)
            c = excl_constraints(wire.src, wire.dst, des.components, fab, g)
            c.append(reaches)
            c.append(dist_constraint)
            result = ms.Solve(ms.And(c))

            #performance suffered a lot with small relaxations -- for now trying complete relaxation
            #relax distance constraints if false
            #TODO: come up with better upper bound on distance
            #variable_dist_factor = 2*__dist_factor
            #while not result and dist < fab.rows*fab.cols:
            #    if verbose:
            #        print('Not routable with given distance constraint, relaxing distance and trying again')
            #    del c[-1]
            #    dist = variable_dist_factor*comp_dist(wire.src, wire.dst, model) + __dist_freedom
            #    dist_constraint = g.distance_leq(fab.getNode(wire.src),fab.getNode(wire.dst), dist)
            #    c.append(dist_constraint)
            #    result = ms.Solve(ms.And(c))
            #    variable_dist_factor = 2*variable_dist_factor

            #do a complete relaxation if not routed
            if not result:
                if verbose:
                    print('Not routable with given distance constraint, relaxing distance and trying again')
                del c[-1]
                result = ms.Solve(ms.And(c))
            
            if result:
            #If the result is SAT, you can find the nodes that make up a satisfying path:
                path_node_names = []
                for node in g.getPath(reaches):
                    path_node_names.append(g.names[node])
                    
                if verbose:
                    print("Satisfying path (as a list of nodes): " + str(path_node_names))

                #increment edge counts
                for edge in g.getPath(reaches, return_edge_lits=True):
                    fab.incrementEdge(edge)
            else:
                heuristic_routable = False
                #TODO: if fail to route, need to reorder and possibly re-place
                if verbose:
                    print('Failed to route')
                    print(g.names[fab.getNode(wire.src)])
                    print(g.names[fab.getNode(wire.dst)])
    return heuristic_routable


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


def test(filepath, fab_dims=(16,16)):
    '''
       Takes a .dot input, parses using dot2smt, places using smtpnr, and routes
    '''
    frows, fcols = fab_dims
    fab = design.Fabric(fab_dims)
    p = placer.Placer(fab)
    model, d = p.place(p.parse_file(filepath))
    fab.setModel(model)
    route(fab, d, model, 2, True)
