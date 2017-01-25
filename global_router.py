from monosat import *
import dot2smt
import smtpnr
import z3
import math

class Fabric:
    def __init__(self, fab_dims):
        self.rows = fab_dims[0]
        self.cols = fab_dims[1]
        self.CLBs = {} 
    def getNode(self, pc):
        return self.CLBs[(pc.pos[0], pc.pos[1])] #return the monosat node associated with that component

class PlacedComp:
    def __init__(self, pos, adj=()):
        self.pos = pos
        self.adj = set(adj)
    def dist(self, pc):
        return abs(self.pos[0] - pc.pos[0]) + abs(self.pos[1] - pc.pos[1])

__dist_factor = 2 #takes two monosat edges for every 1 unit of L1 distance
__dist_freedom = 2 #how many extra edges can be used over the L1 distance between components (2 allows for going around other components)


def build_mgraph(fab, placed_comps):
    '''
        Build a MonoSAT graph. Includes every connection box and switch box but only placed components
        Note: For now, there are connection boxes below and to the right of every CLB and a switch box for each CB
              This is not representative of the true fabric -- will be updated later
    '''
    g = Graph()
    CB = [[0 for x in range(fab.cols)] for y in range(fab.rows)] 
    SB = [[0 for x in range(fab.cols)] for y in range(fab.rows)] 
    #add all the components to the graph
    populate_CLBs(fab, placed_comps, g)
    for y in range(fab.rows):
        for x in range(fab.cols):
            #make top and right connection boxes
            CB[x][y] = (g.addNode('CB({},{})_b'.format(x,y)), g.addNode('CB({},{})_r'.format(x,y))) #(bottom, right)
            #make switch box
            SB[x][y] = g.addNode('SB({},{})'.format(x,y))
            g.addUndirectedEdge(CB[x][y][0], SB[x][y])
            g.addUndirectedEdge(CB[x][y][1], SB[x][y])
            if (x,y) in fab.CLBs:
                g.addUndirectedEdge(fab.CLBs[(x,y)], CB[x][y][0])
                g.addUndirectedEdge(fab.CLBs[(x,y)], CB[x][y][1])
                if x > 0:
                    g.addUndirectedEdge(CB[x-1][y][0], fab.CLBs[(x,y)])
                if y > 0:
                    g.addUndirectedEdge(CB[x][y-1][1], fab.CLBs[(x,y)])
            #TODO only loop through non starting
            if x > 0:
                g.addUndirectedEdge(SB[x-1][y], CB[x][y][1])
            if y > 0:
                g.addUndirectedEdge(SB[x][y-1], CB[x][y][0])
                
    return g


def populate_CLBs(fab, placed_comps, g):
    '''
        add placed components to the fabric
    '''
    for pc in placed_comps:
        fab.CLBs[(pc.pos[0], pc.pos[1])] = g.addNode('CLB({},{})'.format(pc.pos[0],pc.pos[1])) 


def comp_dist(pc, adj):
    '''
        returns the manhattan distance between two components
    '''
    return abs(pc.pos[0] - adj.pos[0]) + abs(pc.pos[1] - adj.pos[1])


def route(fab_dims, placed_comps):
    '''
        attempt to globally (doesn't consider track widths and allows sharing wires) route all of the placed components
    '''
    fab = Fabric(fab_dims)
    g = build_mgraph(fab, placed_comps)
    for pc in placed_comps:
        for pc_out in pc.outputs:
            reaches = g.reaches(fab.getNode(pc),fab.getNode(pc_out))
            dist = g.distance_leq(fab.getNode(pc),fab.getNode(pc_out), __dist_factor*comp_dist(pc, pc_out) + __dist_freedom)
            c = excl_constraints(pc, pc_out, placed_comps, fab, g)
            c.append(reaches)
            c.append(dist)
            result = Solve(And(c))
            print(result)

            if result:
            #If the result is SAT, you can find the nodes that make up a satisfying path:
                path_node_names = []
                for node in g.getPath(reaches):
                    path_node_names.append(g.names[node])
                print("Satisfying path (as a list of nodes): " + str(path_node_names))
    return 


def excl_constraints(src, dst, placed_comps, fab, g):
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
    def _get_x(bv):
        return z3.Extract(frows+fcols-1, frows, bv)

    def _get_y(bv):
        return z3.Extract(frows-1, 0, bv)

    adj = dot2smt.from_file(filepath)
    placed_comps, model = smtpnr.run_test(adj, fab_dims, {1}, True)
    #placed_comps, model = smtpnr.tiny_test()
    for comp in placed_comps:
        comp.pos = (int(math.log(model.eval(_get_x(comp.pos)).as_long(),2)), int(math.log(model.eval(_get_y(comp.pos)).as_long(),2)))

    route(fab_dims, placed_comps)
