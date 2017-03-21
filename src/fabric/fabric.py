import xml.etree.ElementTree as ET
import monosat as ms
import re
from collections import defaultdict
from .fabricfuns import Side, getSide, mapSide, parse_name
from util import IDObject

    
class Element:
    '''
       Interface for PE, CB or SB
    '''
    def __init__(self, x, y, typestr, ports):
        self._x = x
        self._y = y
        self._typestr = typestr
        self._ports = ports
        self._enabled_tracks = {}

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @property
    def typestr(self):
        return self._typestr

    @property
    def ports(self):
        '''
            Returns all input ports
        '''
        return iter(self._ports.values())


class PE(Element):
    '''
       Holds the ports for PEs
    '''
    def __init__(self, x, y, opcode=None):
        super().__init__(x, y, 'PE', dict())
        self._opcode = opcode
        #ports added by parsing input
        #instantiate out port (not explicitly defined in input format)
        self._ports['out'] = Port(Side.NS, None, x, y)

    @property
    def opcode(self):
        return self._opcode

    @opcode.setter
    def opcode(self, op):
        self._opcode = op

    def addPort(self, k, port):
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
        super().__init__(x, y, 'CB', [])


    def addPort(self, port):
        self._ports.append(port)


    @property
    def ports(self):
        return iter(self._ports)
    


class SB(Element):
    '''
       Represents a switch box 
    '''
    def __init__(self, x, y, trk_count):
        super().__init__(x, y, 'SB', dict())
        self._ports[Side.N.value] = [Port(Side.N, t, x, y) for t in range(0, trk_count)]
        self._ports[Side.S.value] = [Port(Side.S, t, x, y) for t in range(0, trk_count)]
        self._ports[Side.E.value] = [Port(Side.E, t, x, y) for t in range(0, trk_count)]
        self._ports[Side.W.value] = [Port(Side.W, t, x, y) for t in range(0, trk_count)]
        self._out_ports = dict()
        self._out_ports[Side.N.value] = None
        self._out_ports[Side.S.value] = None
        self._out_ports[Side.E.value] = None
        self._out_ports[Side.W.value] = None


    def addPort(self, port):
        self._ports[port.side.value][port.track] = port

        
    def getPort(self, side, track):
        if not isinstance(side, Side):
            raise ValueError('Expected a Side but received {}'.format(type(side)))
        
        if side.value in self._ports:
            if self._ports[side.value][track] is not None:
                return self._ports[side.value][track]
            else:
                raise ValueError('Trying to retrieve an uninstantiated port')
                
        else:
            raise ValueError('Expected Side value to be one of {} but received {}'.format(self._ports.keys(), side))

    def getPorts(self, side):
        if side.value in self._ports:
            return self._ports[side.value]
        else:
            raise ValueError('Expected a Side but received {}'.format(type(side)))

    def getOutputPort(self, side, track):
        if not isinstance(side, Side):
            raise ValueError('Expected a Side but received {}'.format(type(side)))
        
        if side.value in self._ports:
            if self._out_ports[side.value][track] is not None:
                return self._out_ports[side.value][track]
            else:
                raise ValueError('Trying to retrieve an uninstantiated port')
                
        else:
            raise ValueError('Expected Side value to be one of {} but received {}'.format(self._ports.keys(), side))

    def getOutputPorts(self, side):
        if side.value in self._out_ports:
            return self._out_ports[side.value]
        else:
            raise ValueError('Expected a Side but received {}'.format(type(side)))

    def setOutputPorts(self, side, ports):
        self._out_ports[side.value] = ports

    @property
    def ports(self):
        c = []
        for ports in self._ports.values():
            c = c + ports
        return iter(c)
                

class Port(IDObject):
    '''
       Holds a side and track number for a particular switch box
       Connecting two nodes from different tiles makes a single track
    '''
    def __init__(self, side, track, x, y):
        super().__init__()
        self._side = side
        self._track = track
        self._x = x
        self._y = y
        if isinstance(side, str):
            self._type_string = side
        elif isinstance(side, Side):
            self._type_string = side.name
        else:
            raise ValueError('Received invalid side type. Expected string or Side '
            'and received {} of type {}'.format(side, type(side)))

    def addEdges(self, g):
        if self._msnode:
            for node in self._nodes:
                self._edges.append(g.addEdge(self._msnode, node.msnode))
        else:
            raise ValueError('MonoSAT node not created, cannot add edges.')


    @property
    def side(self):
        return self._side

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


class Track(IDObject):
    '''
       Holds two nodes describing a single track between switch boxes
       Note: Not directly modeling output nodes of a SB, so this maps an input node
             from one Tile to an input node of another Tile

       ex// instead of (0,0)W_i[0] --> (0,0)E_o[0] --> (1,0)W_i[0]
            it's just  (0,0)W_i[0] --> (1,0)W_i[0]
    '''
    def __init__(self, src, dst, names, element):
        super().__init__()
        self._src = src
        self._dst = dst
        self._names = names
        self._element = element

    @property
    def src(self):
        return self._src

    @property
    def dst(self):
        return self._dst

    @property
    def names(self):
        return self._names

    @property
    def element(self):
        return self._element

    def enable(self):
        self._element._enabled_tracks[self._names[0]] = self._names[1]

    def __repr__(self):
        return '{} --> {}'.format(self._names[0], self._names[1])


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
        self._CB = dict()
        
        self._PE_used = False

    def addTrack(self, src, snk, names, element):
        self._tracks.append(Track(src, snk, names, element))

    def enablePE(self):
        self._PE_used = True
        for port in self._CB['a'].ports:
            src = '{}_i[{}]'.format(port.side.name, str(port.track))
            self.addTrack(port, self._PE.getPort('a'), (src, 'PE_a'), self._CB['a'])
        for port in self._CB['b'].ports:
            src = '{}_i[{}]'.format(port.side.name, str(port.track))
            self.addTrack(port, self._PE.getPort('b'), (src, 'PE_b'), self._CB['b'])

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
    def CB(self):
        return self._CB

    @property
    def SB(self):
        return self._SB


class Fabric:
    '''
       Class describing physical fabric as collection of Tiles
    '''
    def __init__(self):
        self._Tiles = dict()
        self._width = 0
        self._height = 0

    def __getitem__(self, xy_loc):
        return self._Tiles[xy_loc]

    def __setitem__(self, xy_loc, tile):
        self._Tiles[xy_loc] = tile
        if xy_loc[0] > self._width:
            self._width = xy_loc[0] + 1
        if xy_loc[1] > self._height:
            self._height = xy_loc[1] + 1

    @property
    def width(self):
        return self._width

    @property
    def height(self):
        return self._height

    @property
    def rows(self):
        return self._height

    @property
    def cols(self):
        return self._width
    
    @property
    def Tiles(self):
        return self._Tiles



def parseXML(filepath):
    '''
       Reads an input file and outputs a fabric
    '''
    N = Side.N
    S = Side.S
    E = Side.E
    W = Side.W
    
    tree = ET.parse(filepath)
    root = tree.getroot()

    fab = Fabric()
    #Initialize tiles
    for tile in root:
        x = int(tile.get('row'))
        y = int(tile.get('col'))
        tracks = tile.get('tracks').split()
        num_tracks = {}
        for track in tracks:
            tr = track.split(':')
            num_tracks[tr[0]] = tr[1]
        fab[(x,y)] = Tile(x, y, int(num_tracks['BUS16']))


    #make input/output connections
    #i.e. E_o[0] --> W_i[0]
    #Note coordinate system has origin in upper left corner
    width = fab.width
    height = fab.height
    for x in range(width):
        for y in range(height):
            tile = fab[(x,y)]
            if y < height-1:
                tile.SB.setOutputPorts(S, fab[(x, y+1)].SB.getPorts(N))
            else:
                #off the board: instantiate ports for pins
                tile.SB.setOutputPorts(S, [Port(N, t, x, y+1) for t in range(tile.trk_count)])

            if y > 0:
                tile.SB.setOutputPorts(N, fab[(x, y-1)].SB.getPorts(S))
            else:
                tile.SB.setOutputPorts(N, [Port(S, t, x, y-1) for t in range(tile.trk_count)])
                
            if x < width-1:
                tile.SB.setOutputPorts(E, fab[(x+1, y)].SB.getPorts(W))
            else:
                tile.SB.setOutputPorts(E, [Port(E, t, x+1, y) for t in range(tile.trk_count)])

            if x > 0:
                tile.SB.setOutputPorts(W, fab[(x-1, y)].SB.getPorts(E))
            else:
                tile.SB.setOutputPorts(W, [Port(W, t, x-1, y) for t in range(tile.trk_count)])
        
    for tile in root:
        x = int(tile.get('col'))
        y = int(tile.get('row'))
        t = fab[(x,y)]
        for cb in tile.findall('cb'):
            feature_address = int(cb.get('feature_address'))
            sel_width = int(cb.find('sel_width').text)
            if cb.get('bus') == 'BUS16':
                for mux in cb.findall('mux'):
                    snk = mux.get('snk')
                    t.PE.addPort(snk, Port(Side.NS, None, x, y))
                    for src in mux.findall('src'):
                        sel = int(src.get('sel'))
                        port = src.text
                        direc, bus, side, track = parse_name(port)
                        t.CB[snk] = CB(x,y)
                        t.CB[snk].addPort(t.SB.getPort(side, track))
                        t.addTrack(t.SB.getPort(side, track), t.PE.getPort(snk), (port, snk), t.CB[snk])
                    

        #not reading opcode yet (only writing it)

        #not reading pe features yet (assuming homogenous for now)


        for sb in tile.findall('sb'):
            feature_address = int(sb.get('feature_address'))
            sel_width = int(sb.find('sel_width').text)
            if sb.get('bus') == 'BUS16':
                for mux in sb.findall('mux'):
                    snk = mux.get('snk')
                    snk_direc, snk_bus, snk_side, snk_track = parse_name(snk)
                    for src in mux.findall('src'):
                        sel = int(src.get('sel'))
                        port = src.text
                        if port[0:2] == 'pe':
                            t.addTrack(t.PE.getPort('out'), t.SB.getOutputPort(snk_side, snk_track), (port, snk), t.SB)
                        else:
                            src_direc, src_bus, src_side, src_track = parse_name(port)
                            t.addTrack(t.SB.getPort(src_side, src_track), t.SB.getOutputPort(snk_side, snk_track), (port, snk), t.SB)
                        

                    for ft in sb.findall('ft'):
                        snk = ft.get('snk')
                        #since it's a feedthrough, there should be exactly one source
                        src = ft.find('src').text
                        snk_direc, snk_bus, snk_side, snk_track = parse_name(snk)
                        src_direc, src_bus, src_side, src_track = parse_name(src)
                        t.addTrack(t.SB.getPort(src_side, src_track), t.SB.getOutputPort(snk_side, snk_track), (src, snk), t.SB)

    return fab
                


#deprecated -- will be switched to PNR object
def build_msgraph(fab, g, used_PEs):
    msnodes = dict()
    edge2track = dict()
    #add msnodes for all the used PEs first (because special naming scheme)
    for x in range(fab.width):
        for y in range(fab.height):
            if (x, y) in used_PEs:
                #fab[(x, y)].enablePE() #adds tracks for PE input and output
                msnodes[fab[(x, y)].PE.getPort('a')] = g.addNode('({},{})PE_a'.format(x, y))
                msnodes[fab[(x, y)].PE.getPort('b')] = g.addNode('({},{})PE_b'.format(x, y))
                msnodes[fab[(x, y)].PE.getPort('out')] = g.addNode('({},{})PE_out'.format(x, y))

    for tile in fab.Tiles.values(): 
        for track in tile.tracks:
            src = track.src
            dst = track.dst
            if src not in msnodes:
                msnodes[src] = g.addNode('({},{}){}_i[{}]'.format(str(src.x), str(src.y), src.side.name, str(src.track)))
            if dst not in msnodes:
                msnodes[dst] = g.addNode('({},{}){}_i[{}]'.format(str(dst.x), str(dst.y), dst.side.name, str(dst.track)))

            #print('{}-->{}'.format(g.names[msnodes[src]], g.names[msnodes[dst]]))
            e = g.addEdge(msnodes[src], msnodes[dst])
            edge2track[e.lit] = track
    return msnodes, edge2track






