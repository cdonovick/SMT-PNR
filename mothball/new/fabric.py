import xml.etree.ElementTree as ET
from enum import Enum
import monosat as ms
import re


class Direction(Enum):
    N = 0
    S = 1
    E = 2
    W = 3


def getDir(direction_str):
    if direction_str == 'N':
        return Direction.N
    elif direction_str == 'S':
        return Direction.S
    elif direction_str == 'E':
        return Direction.E
    elif direction_str == 'W':
        return Direction.W
    else:
        raise ValueError('Not passed a valid direction string')


class Node:
    def __init__(self, direction, track, x, y):
        self._nodes = []
        self._msnode = None
        self._edges = []
        self._direction = direction
        self._track = track
        self._x = x
        self._y = y
        if direction is None and track is None:
            self._type_string = 'PE'
        else:
            self._type_string = direction.name

    def addEdges(self, g):
        if self._msnode:
            for node in self._nodes:
                self._edges.append(g.addEdge(self._msnode, node.msnode))
        else:
            raise ValueError('MonoSAT node not created, cannot add edges.')

    @property
    def nodes(self):
        return self._nodes

    @property
    def msnode(self):
        return self._msnode

    @msnode.setter
    def msnode(self, msnode):
        self._msnode = msnode

    @property
    def edges(self):
        return self._edges

    @property
    def direction(self):
        return self._direction

    @property
    def track(self):
        return self._track

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @property
    def type_string(self):
        return self._type_string


class Wire:
    def __init__(self, src, dst):
        self._src = src
        self._dst = dst

    @property
    def src(self):
        return self._src

    @property
    def dst(self):
        return self._dst

    def __repr__(self):
        return '{} -[{}]-> {}'.format(self.src.name, self.width, self.dst.name)


class Tile:
    def __init__(self, x, y, trk_count, PE_used):
        self._x = x
        self._y = y
        self._NTile = None
        self._STile = None
        self._ETile = None
        self._WTile = None
        self._trk_count = trk_count
        self._wires = []
        self._input_nodes = self.initNodes()
        self._output_nodes = 4*[[]]
        if PE_used:
            self._PE_i = Node(None, None, x, y)
            self._PE_o = Node(None, None, x, y)
            for direc in self._input_nodes:
                for node in direc:
                    self._wires.append(Wire(node, self._PE_i))
        else:
            self._PE = None

    def initNodes(self):
        #create nodes indexed by direction enum value and track
        #each tile has all input nodes
        input_nodes = [[Node(Direction(d),i, self._x, self._y) for i in range(self._trk_count)] for d in range(4)]
        
        #deprecated because caused ordering problems
        #connect to PE
        #for direc in input_nodes:
        #    for node in direc:
        #        self._wires.append(Wire(node, self._PE))
        return input_nodes

    @property
    def NTile(self):
        return self._NTile

    @NTile.setter
    def NTile(self, Tile):
        self._NTile = Tile

    @property
    def STile(self):
        return self._STile

    @STile.setter
    def STile(self, Tile):
        self._STile = Tile

    @property
    def ETile(self):
        return self._ETile

    @ETile.setter
    def ETile(self, Tile):
        self._ETile = Tile

    @property
    def WTile(self):
        return self._WTile

    @WTile.setter
    def WTile(self, Tile):
        self._WTile = Tile

    def addWire(self, src, snk):
        self._wires.append(Wire(src, snk))

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @property
    def trk_count(self):
        return self._trk_count

    @property
    def wires(self):
        return self._wires

    @property
    def PE_i(self):
        return self._PE_i

    @property
    def PE_o(self):
        return self._PE_o

    @property
    def input_nodes(self):
        return self._input_nodes

    @property
    def output_nodes(self):
        return self._output_nodes


class Fabric:
    def __init__(self, width, height, used_PEs):
        self._width = width
        self._height = height
        self._used_PEs = used_PEs
        self._Tiles = [[None for y in range(height)] for x in range(width)]

    @property
    def width(self):
        return self._width

    @property
    def height(self):
        return self._height

    @property
    def used_PEs(self):
        return self._used_PEs

    @property
    def Tiles(self):
        return self._Tiles

    def setTile(self, Tile):
        if self._Tiles[Tile.x][Tile.y] is None:
            self._Tiles[Tile.x][Tile.y] = Tile
        else:
            raise ValueError('Fabric already has a tile set at ({},{})'.format(Tile.x, Tile.y))


def parseXML(filepath, used_PEs):
    N = Direction.N
    S = Direction.S
    E = Direction.E
    W = Direction.W
    
    tree = ET.parse(filepath)
    root = tree.getroot()
    width = int(root.get('width'))
    height = int(root.get('height'))
    fab = Fabric(width, height, used_PEs)
    for child in root:
        x = int(child.get('x'))
        y = int(child.get('y'))
        trk_count = int(child.get('trk_cnt'))
        used = (x,y) in used_PEs
        fab.setTile(Tile(x, y, trk_count, used))

    #make tile connections and input/output connections
    #i.e. E_o[0] --> W_i[0]
    for x in range(width):
        for y in range(height):
            tile = fab.Tiles[x][y]
            if y < height-1:
                tile.STile = fab.Tiles[x][y+1]
                tile.output_nodes[S.value] = tile.STile.input_nodes[N.value]
            else:
                tile.output_nodes[S.value] = [Node(N,i, x, y+1) for i in range(tile.trk_count)]

            if y > 0:
                tile.NTile = fab.Tiles[x][y-1]
                tile._output_nodes[N.value] = fab.Tiles[x][y-1].input_nodes[S.value]
            else:
                tile._output_nodes[N.value] = [Node(S,i, x, y-1) for i in range(tile.trk_count)]
                
            if x < width-1:
                tile.ETile = fab.Tiles[x+1][y]
                tile.output_nodes[E.value] = fab.Tiles[x+1][y].input_nodes[W.value]
            else:
                tile.output_nodes[E.value] = [Node(E,i, x+1, y) for i in range(tile.trk_count)]

            if x > 0:
                tile.WTile = fab.Tiles[x-1][y]
                tile.output_nodes[W.value] = fab.Tiles[x-1][y].input_nodes[E.value]
            else:
                tile.output_nodes[W.value] = [Node(W,i, x-1, y) for i in range(tile.trk_count)]

    for sb in root:
        x = int(sb.get('x'))
        y = int(sb.get('y'))
        for direc in sb:
            for mux in direc:
                snk = mux.find('snk').text
                dsnk = getDir(snk[0])
                trksnk = int(re.findall('\d+', snk)[0])
                snk_node = fab.Tiles[x][y].output_nodes[dsnk.value][trksnk]
                for src in mux.findall('src'):
                    s = src.text
                    if s != 'PE':
                        d = getDir(s[0])
                        trk = int(re.findall('\d+', s)[0])
                        src_node = fab.Tiles[x][y].input_nodes[d.value][trk]
                        fab.Tiles[x][y].addWire(src_node, snk_node)
                    elif (x, y) in used_PEs:
                        fab.Tiles[x][y].addWire(fab.Tiles[x][y].PE_o, snk_node)

    return fab


def build_msgraph(fab, g):
    #add msnodes for all the used PEs first (because special naming scheme)
    for col in fab.Tiles:
        for tile in col:
            if (tile.x, tile.y) in fab.used_PEs:
                tile.PE_i.msnode = g.addNode('({},{})PE_i'.format(tile.x, tile.y))
                tile.PE_o.msnode = g.addNode('({},{})PE_o'.format(tile.x, tile.y))
    for column in fab.Tiles:
        for tile in column:
            #deprecated -- just handling them all as wires now
            #connect all inputs to PE
            #tile.PE.msnode = g.addNode('(' + str(tile.x) + ',' + str(tile.y) + ')PE')
            #for direc in tile.input_nodes:
            #    for node in direc:
            #        if node.msnode is None:
            #            node.msnode = g.addNode('({},{}){}_i[{}]'.format(str(node.x), str(node.y), node.type_string, str(node.track)))
            #        g.addEdge(node.msnode, tile.PE.msnode)
            #connect all inputs to outputs 
            for wire in tile.wires:
                src = wire.src
                dst = wire.dst
                if src.msnode is None:
                    src.msnode = g.addNode('({},{}){}_i[{}]'.format(str(src.x), str(src.y), src.type_string, str(src.track)))
                if dst.msnode is None:
                    dst.msnode = g.addNode('({},{}){}_i[{}]'.format(str(dst.x), str(dst.y), dst.type_string, str(dst.track)))
                if src.type_string is not 'PE' and dst.type_string is not 'PE':
                    g.addUndirectedEdge(src.msnode, dst.msnode)
                else:
                    g.addEdge(src.msnode, dst.msnode)
    return g


def mapDir(x, y, direction):
    if direction is Direction.N:
        return x, y+1, Direction.S
    elif direction is Direction.S:
        return x, y-1, Direction.N
    elif direction is Direction.E:
        return x+1, y, Direction.W
    elif direction is Direction.W:
        return x-1, y, Direction.E
    else:
        raise ValueError('Expected a Direction but got {}'.format(type(direction)))
