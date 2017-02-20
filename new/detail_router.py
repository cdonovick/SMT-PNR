import z3
import z3util as zu
import pnr2dot
import re
import math

class Track:
    count = {}
    def __init__(self, bounding_nodes, name, start_node, W):
        if bounding_nodes in Track.count:
            Track.count[bounding_nodes] += 1
            self._unique_name = name + str(Track.count[bounding_nodes])
        else:
            self._unique_name = name + '1'
            Track.count[bounding_nodes] = 1
        self._name = name
        self._start_node = start_node
        self._var = z3.BitVec(self._unique_name, int(math.ceil(math.log2(W))))

    @property
    def name(self):
        return self._name

    @property
    def unique_name(self):
        return self._unique_name

    @property
    def start_node(self):
        return self._start_node

    @property
    def var(self):
        return self._var


def create_tracks(routes, W):
    #given nodes with associated paths
    tracks = {}
    constraints = []
    for node in routes:
        for path in routes[node]:
            start_node = path[0]
            bounding_nodes = frozenset([path[0], path[1]])
            name = path[0] + '--' + path[1]
            #location = tuple(re.findall('(\d+,\d+)', name))
            if bounding_nodes not in tracks:
                tracks[bounding_nodes] = []
            t = Track(bounding_nodes, name, start_node, W)
            tracks[bounding_nodes].append(t)
            for i in range(1, len(path)-1):
                bounding_nodes = frozenset([path[i], path[i+1]])
                name = path[i] + '--' + path[i+1]
                #location = tuple(re.findall('(\d+,\d+)', name))
                if bounding_nodes not in tracks:
                    tracks[bounding_nodes] = []
                    t2 = Track(bounding_nodes, name, start_node, W)
                    tracks[bounding_nodes].append(t2)
                else:
                    t2 = Track(bounding_nodes, name, start_node, W)
                    tracks[bounding_nodes].append(t2)
                    #don't include paths originating from same node (for now assuming only one output)
                    start_nodes = {start_node}
                    for track in tracks[bounding_nodes]:
                        #don't need to add multiple distincts for same start_node
                        if track.start_node not in start_nodes:
                            #if sharing segment, don't let track assignments be the same
                            constraints.append(z3.Distinct(t2.var, track.var))
                            start_nodes.update(track.start_node)
                #since in same path and assuming planar switches, they must be equal
                constraints.append(t.var == t2.var)
                t = t2
    return tracks, constraints


def detailed_route(paths, W):
    node_paths = {}
    for path in paths:
        if path[0] in node_paths:
            node_paths[path[0]].append(path)
        else:
            node_paths[path[0]] = [path]
    tracks, constraints = create_tracks(node_paths, W)
    s = z3.Solver()
    s.add(z3.And(constraints))
    if s.check() != z3.sat:
        print('Could not find satisfying detailed route')
    else:
        print('Found satisfying detailed routing')
        return s.model()
        #print(s.model())
