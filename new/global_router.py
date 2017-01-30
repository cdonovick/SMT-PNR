import monosat as ms
import design
import placer
import z3
import math

class MFabric:
    def __init__(self, fab_dims, model):
        self.rows = fab_dims[0]
        self.cols = fab_dims[1]
        self.CLBs = {}
        self.model = model
        
    def getNode(self, pc):
        return self.CLBs[pc.pos.get_coordinates( self.model)] #return the monosat node associated with that component
    
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
            #connect connection boxes and switch boxes
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
            if x > 0 and x < fab.cols - 1 and y < fab.rows - 1:
                g.addUndirectedEdge(SB[x-1][y], CBb[x][y])
            if y > 0 and x < fab.cols - 1 and y < fab.rows - 1:
                g.addUndirectedEdge(SB[x][y-1], CBr[x][y])
    return g


def comp_dist(pc, adj, model):
    '''
        returns the manhattan distance between two components
    '''
    pcpos = pc.pos.get_coordinates(model)
    adjpos = adj.pos.get_coordinates(model)
    return abs(pcpos[0] - adjpos[0]) + abs(pcpos[1] - adjpos[1])


def route(fab_dims, des, model):
    '''
        attempt to globally (doesn't consider track widths and allows sharing wires) route all of the placed components
    '''
    fab = MFabric(fab_dims, model)
    g = build_mgraph(fab, des.components)
    for pc in des.components:
        for wire in pc.outputs:
            reaches = g.reaches(fab.getNode(wire.src),fab.getNode(wire.dst))
            dist = g.distance_leq(fab.getNode(wire.src),fab.getNode(wire.dst), __dist_factor*comp_dist(wire.src, wire.dst, model) + __dist_freedom)
            c = excl_constraints(wire.src, wire.dst, des.components, fab, g)
            c.append(reaches)
            c.append(dist)
            result = ms.Solve(ms.And(c))
            print(result)

            if result:
            #If the result is SAT, you can find the nodes that make up a satisfying path:
                path_node_names = []
                for node in g.getPath(reaches):
                    path_node_names.append(g.names[node])
                print("Satisfying path (as a list of nodes): " + str(path_node_names))
    return 


def excl_constraints(src, dest, placed_comps, fab, g):
    '''
        generate the constraints that components other than the source and destination cannot be used in routing
    '''
    c = []
    for p in placed_comps:
        if p != src and p != dest:
            c.append(~g.reaches(fab.getNode(src), fab.getNode(p)))
    return c


def test(filepath, fab_dims=(16,16)):
    '''
       Takes a .dot input, parses using dot2smt, places using smtpnr, and routes
    '''
    frows, fcols = fab_dims
    fab = design.Fabric(fab_dims)
    p = placer.Placer(fab)
    d, model = p.place(p.parse_file(filepath))
    route(fab_dims, d, model)
