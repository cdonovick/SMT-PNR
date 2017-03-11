import xml.etree.ElementTree as ET
from enum import Enum
import monosat as ms
import re
from collections import defaultdict
from classutil import IDObject


class Direction(Enum):
    N = 0
    S = 1
    E = 2
    W = 3
    ND = 4 #no direction


def getDir(direction_str):
    '''
       Takes a string and returns the corresponding direction
    '''
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


class Element:
    '''
       Interface for PE, CB or SB
    '''
    def __init__(self, x, y, ports=dict()):
        self._x = x
        self._y = y
        self._ports = ports

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @property
    def ports(self):
        '''
            Returns all ports
        '''
        return iter(self._ports.values())


class PE(Element):
    #add an opcode field
    def __init__(self, x, y, opcode=None):
        super().__init__(x, y)
        self._opcode = opcode
        #instantiate ports with no direction
        self._ports['V'] = Port(Direction.ND, None)
        self._ports['H'] = Port(Direction.ND, None)
        self._ports['out'] = Port(Direction.ND, None)

    @property
    def opcode(self):
        return self._opcode

    @opcode.setter
    def opcode(self, op):
        self._opcode = op

    def addPort(self, k, port):
        if k not in self._ports:
            raise ValueError('Expected one of {}, but received {}'.format(self._ports.keys(), k))
        self._ports[k] = port

    def getPort(self, k):
        if k in self._ports and self._ports[k] is not None:
            return self._ports[k]
        elif self._ports[k] is None:
            raise ValueError('Tried to get an uninstantiated port')
        else:
            raise ValueError('Expected one of {} but received {}'.format(self._ports.keys(), k))
    

class CB(Element):
    '''
       Represents a connection box
    '''
    def __init__(self, x, y):
        super().__init__(x, y, [])
        #create the output port
        self._output_port = Port(Direction.ND, None) 


    def addPort(self, port):
        self._ports.append(port)


    @property
    def output_port(self):
        return self._output_port

    @property
    def ports(self):
        return iter(self._ports)
    


class SB(Element):
    '''
       Represents a switch box 
    '''
    def __init__(self, x, y, trk_count, ports=dict()):
        super().__init__(x, y, ports)
        self._ports[Direction.N.value] = [Port(Direction.N, x) for x in range(0, trk_count)]
        self._ports[Direction.S.value] = [Port(Direction.S, x) for x in range(0, trk_count)]
        self._ports[Direction.E.value] = [Port(Direction.E, x) for x in range(0, trk_count)]
        self._ports[Direction.W.value] = [Port(Direction.W, x) for x in range(0, trk_count)]
        self._out_ports = dict()
        self._out_ports[Direction.N.value] = None
        self._out_ports[Direction.S.value] = None
        self._out_ports[Direction.E.value] = None
        self._out_ports[Direction.W.value] = None


    def addPort(self, port):
        self._ports[port.direction.value][port.track] = port

        
    def getPort(self, direction, track):
        if not isinstance(direction, Direction):
            raise ValueError('Expected a Direction but received {}'.format(type(direction)))
        
        if direction.value in self._ports:
            if self._ports[direction.value][track] is not None:
                return self._ports[direction.value][track]
            else:
                raise ValueError('Trying to retrieve an uninstantiated port')
                
        else:
            raise ValueError('Expected Direction value to be one of {} but received {}'.format(self._ports.keys(), direction))

    def getPorts(self, direction):
        if direction.value in self._ports:
            return self._ports[direction.value]
        else:
            raise ValueError('Expected a Direction but received {}'.format(type(direction)))

    def getOutputPort(self, direction, track):
        if not isinstance(direction, Direction):
            raise ValueError('Expected a Direction but received {}'.format(type(direction)))
        
        if direction.value in self._ports:
            if self._out_ports[direction.value][track] is not None:
                return self._out_ports[direction.value][track]
            else:
                raise ValueError('Trying to retrieve an uninstantiated port')
                
        else:
            raise ValueError('Expected Direction value to be one of {} but received {}'.format(self._ports.keys(), direction))

    def getOutputPorts(self, direction):
        if direction.value in self._out_ports:
            return self._out_ports[direction.value]
        else:
            raise ValueError('Expected a Direction but received {}'.format(type(direction)))

    def setOutputPorts(self, direction, ports):
        self._out_ports[direction.value] = ports

    @property
    def ports(self):
        c = []
        for ports in self._ports.values():
            c = c + ports
        return iter(c)
                

class Port(IDObject):
    '''
       Holds a direction and track number for a particular switch box
       Connecting two nodes from different tiles makes a single track
    '''
    def __init__(self, direction, track):
        super().__init__()
        self._msnode = None
        self._direction = direction
        self._track = track
        if isinstance(direction, str):
            self._type_string = direction
        elif isinstance(direction, Direction):
            self._type_string = direction.name
        else:
            raise ValueError('Received invalid direction type. Expected string or Direction '
            'and received {} of type {}'.format(direction, type(direction)))

    def addEdges(self, g):
        if self._msnode:
            for node in self._nodes:
                self._edges.append(g.addEdge(self._msnode, node.msnode))
        else:
            raise ValueError('MonoSAT node not created, cannot add edges.')

    @property
    def msnode(self):
        return self._msnode

    @msnode.setter
    def msnode(self, msnode):
        self._msnode = msnode

    @property
    def direction(self):
        return self._direction

    @property
    def track(self):
        return self._track

    @property
    def type_string(self):
        return self._type_string


class Track:
    '''
       Holds two nodes describing a single track between switch boxes
       Note: Not directly modeling output nodes of a SB, so this maps an input node
             from one Tile to an input node of another Tile

       ex// instead of (0,0)W_i[0] --> (0,0)E_o[0] --> (1,0)W_i[0]
            it's just  (0,0)W_i[0] --> (1,0)W_i[0]
    '''
    def __init__(self, src, dst):
        self._src = src
        self._dst = dst
        if isinstance(dst, list):
            print('dst is a list')

    @property
    def src(self):
        return self._src

    @property
    def dst(self):
        return self._dst

    def __repr__(self):
        return '{} --> {}'.format(self.src.name, self.dst.name)


class Tile:
    '''
       Class that holds PE's, CBs, SBs and nodes that define SB interconnect
    '''
    def __init__(self, x, y, trk_count):
        self._x = x
        self._y = y
        self._trk_count = trk_count
        self._tracks = []
        self._PE = PE(x, y)
        self._SB = SB(x, y, trk_count)
        self._CBV = CB(x, y)
        self._CBH = CB(x, y)

        #add switch box ports to connection boxes
        #for now, connection boxes are just aliases for
        #ports coming from nearby switch boxes
        for port in self._SB.getPorts(Direction.N):
            self._CBV.addPort(port)

        for port in self._SB.getPorts(Direction.S):
            self._CBV.addPort(port)

        for port in self._SB.getPorts(Direction.E):
            self._CBH.addPort(port)

        for port in self._SB.getPorts(Direction.W):
            self._CBH.addPort(port)
        
        self._PE_used = False

    def addTrack(self, src, snk):
        self._tracks.append(Track(src, snk))

    def enablePE(self):
        self._PE_used = True
        for port in self._CBV.ports:
            self.addTrack(port, self._PE.getPort('V'))
        for port in self._CBH.ports:
            self.addTrack(port, self._PE.getPort('H'))
        for port in self._SB.ports:
            self.addTrack(self._PE.getPort('out'), port)

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
    def tracks(self):
        return self._tracks

    @property
    def PE(self):
        return self._PE

    @property
    def CBV(self):
        return self._CBV

    @property
    def CBH(self):
        return self._CBH

    @property
    def SB(self):
        return self._SB


class Fabric:
    '''
       Class describing physical fabric as collection of Tiles
    '''
    def __init__(self, width, height):
        self._width = width
        self._height = height
        self._Tiles = dict()

    def __getitem__(self, xy_loc):
        return self._Tiles[xy_loc]

    def __setitem__(self, xy_loc, tile):
        self._Tiles[xy_loc] = tile

    @property
    def width(self):
        return self._width

    @property
    def height(self):
        return self._height

    @property
    def Tiles(self):
        return self._Tiles

    #deprecated -- replaced with dictionary
    #def setTile(self, Tile):
    #    if self._Tiles[Tile.x][Tile.y] is None:
    #        self._Tiles[Tile.x][Tile.y] = Tile
    #    else:
    #        raise ValueError('Fabric already has a tile set at ({},{})'.format(Tile.x, Tile.y))


def parseXML(filepath):
    '''
       Returns a fabric
       filepath: xml file of sparse connectivity matrix
       (deprecated) used_PEs: set of locations that are used
    '''

    #TODO: Need to add ports to used PEs and tracks between connection boxes and PEs
    
    N = Direction.N
    S = Direction.S
    E = Direction.E
    W = Direction.W
    
    tree = ET.parse(filepath)
    root = tree.getroot()
    width = int(root.get('width'))
    height = int(root.get('height'))
    fab = Fabric(width, height)
    for child in root:
        x = int(child.get('x'))
        y = int(child.get('y'))
        trk_count = int(child.get('trk_cnt'))
        #used = (x,y) in used_PEs
        #fab.setTile(Tile(x, y, trk_count, used))
        fab[(x,y)] = Tile(x, y, trk_count)

    #make tile connections and input/output connections
    #i.e. E_o[0] --> W_i[0]
    #Note coordinate system has origin in upper left corner
    for x in range(width):
        for y in range(height):
            tile = fab[(x,y)]
            if y < height-1:
                tile.SB.setOutputPorts(S, fab[(x, y+1)].SB.getPorts(N))
            else:
                #off the board: instantiate ports for pins
                tile.SB.setOutputPorts(S, [Port(N, t) for t in range(tile.trk_count)])

            if y > 0:
                tile.SB.setOutputPorts(N, fab[(x, y-1)].SB.getPorts(S))
            else:
                tile.SB.setOutputPorts(N, [Port(S, t) for t in range(tile.trk_count)])
                
            if x < width-1:
                tile.SB.setOutputPorts(E, fab[(x+1, y)].SB.getPorts(W))
            else:
                tile.SB.setOutputPorts(E, [Port(E, t) for t in range(tile.trk_count)])

            if x > 0:
                tile.SB.setOutputPorts(W, fab[(x-1, y)].SB.getPorts(E))
            else:
                tile.SB.setOutputPorts(W, [Port(W, t) for t in range(tile.trk_count)])

    for sb in root:
        x = int(sb.get('x'))
        y = int(sb.get('y'))
        for direc in sb:
            for mux in direc:
                snk = mux.find('snk').text
                dsnk = getDir(snk[0])
                trksnk = int(re.findall('\d+', snk)[0])
                
                if fab[(x, y)].SB.getOutputPorts(dsnk) is not None:
                    snk_node = fab[(x, y)].SB.getOutputPort(dsnk, trksnk)
                    for src in mux.findall('src'):
                        s = src.text
                        if s != 'PE':
                            d = getDir(s[0])
                            trk = int(re.findall('\d+', s)[0])
                            src_node = fab[(x, y)].SB.getPort(d, trk)
                            fab[(x,y)].addTrack(src_node, snk_node)
                        #elif (x, y) in used_PEs:
                        #    fab.Tiles[x][y].addTrack(fab.Tiles[x][y].PE_o, snk_node)

    return fab


#deprecated -- will be switched to PNR object
def build_msgraph(fab, g, used_PEs):
    msnodes = dict()
    #add msnodes for all the used PEs first (because special naming scheme)
    for x in range(fab.width):
        for y in range(fab.height):
            if (x, y) in used_PEs:
                fab[(x, y)].enablePE() #adds tracks for PE input and output
                msnodes[fab[(x, y)].PE.getPort('V')] = g.addNode('({},{})PE_V'.format(x, y))
                msnodes[fab[(x, y)].PE.getPort('H')] = g.addNode('({},{})PE_H'.format(x, y))
                msnodes[fab[(x, y)].PE.getPort('out')] = g.addNode('({},{})PE_out'.format(x, y))
                msnodes[fab[(x, y)].CBV.output_port] = g.addNode('({},{})CBV'.format(x,y))
                msnodes[fab[(x, y)].CBH.output_port] = g.addNode('({},{})CBH'.format(x,y))

    for tile in fab.Tiles.values(): 
        for track in tile.tracks:
            src = track.src
            dst = track.dst
            if src not in msnodes:
                msnodes[src] = g.addNode('({},{}){}_i[{}]'.format(str(tile.x), str(tile.y), src.direction.name, str(src.track)))
            if dst not in msnodes:
                msnodes[dst] = g.addNode('({},{}){}_i[{}]'.format(str(tile.x), str(tile.y), dst.direction.name, str(dst.track)))
            g.addEdge(msnodes[src], msnodes[dst])
    return msnodes


def mapDir(x, y, direction):
    '''
       Given a location and a direction, returns the receiving tile location and receiving direction
    '''
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
