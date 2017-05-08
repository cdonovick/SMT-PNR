import lxml.etree as ET
from util import IDObject
from .fabricfuns import Side, mapSide, parse_name


class Port(IDObject):
    '''
       Represents a port on a fabric
    '''
    def __init__(self, x, y):
        super().__init__()
        self._x = x
        self._y = y

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @property
    def loc(self):
        return (self._x, self._y)

    @property
    def __repr__(self):
        return str(self.loc) + 'port'


class Track(IDObject):
    '''
       Holds two ports describing a single track between them
    '''
    def __init__(self, src, dst, wire_names, parent):
        super().__init__()
        self._src = src
        self._dst = dst
        self._wire_names = wire_names
        self._parent = parent

    @property
    def src(self):
        return self._src

    @property
    def dst(self):
        return self._dst

    @property
    def wire_names(self):
        return self._wire_names

    @property
    def parent(self):
        return self._parent

    def __repr__(self):
        return self.parent + str(self.src.loc) + \
            '-T={}->'.format(self.track_num) + str(self.dst.loc)


class Fabric:
    def __init__(self, rows, cols, sources, sinks, routable, tracks):
        self._rows = rows
        self._cols = cols
        self._sources = sources
        self._sinks = sinks
        self._routable = routable
        self._tracks = tracks

    @property
    def rows(self):
        return self._rows

    @property
    def cols(self):
        return self._cols

    @property
    def height(self):
        ''' alias for rows'''
        return self._rows

    @property
    def width(self):
        ''' alias for cols'''
        return self._cols

    @property
    def sources(self):
        return self._sources

    @property
    def sinks(self):
        return self._sinks

    @property
    def routable(self):
        return self._routable

    @property
    def tracks(self):
        return self._tracks


def parse_xml(filepath):
    N = Side.N
    S = Side.S
    E = Side.E
    W = Side.W
    sides = [N, S, E, W]

    tree = ET.parse(filepath)
    root = tree.getroot()

    rows, cols, num_tracks = pre_process(root)

    params = {'rows': rows, 'cols': cols, 'num_tracks': num_tracks, 'sides': sides,
              'sinksBUS16': dict(), 'sourcesBUS16': dict(), 'routableBUS16': dict()}

    SB, PE = generate_layer('BUS16', params)
    params['SBBUS16'] = SB
    params['PEBUS16'] = PE

    connect_tiles('BUS16', params)

    params['tracksBUS16'] = list()

    connect_pe(root, 'BUS16', params)

    connect_sb(root, 'BUS16', params)

    return Fabric(rows, cols, params['sourcesBUS16'], params['sinksBUS16'], params['routableBUS16'], params['tracksBUS16'])


def pre_process(root):
    rows = 0
    cols = 0
    num_tracks = dict()
    for tile in root:
        # Not assuming tiles are in order
        # Although one would hope they are
        r = int(tile.get('row'))
        c = int(tile.get('col'))
        if r > rows:
            rows = r
        if c > cols:
            cols = c
        tracks = tile.get('tracks').split()
        for track in tracks:
            tr = track.split(':')
            # still indexing as x, y for now
            # i.e. col, row
            num_tracks[(c, r, tr[0])] = int(tr[1])

    # rows and cols are the number not the index
    return rows + 1, cols + 1, num_tracks


def generate_layer(BUS, params):
    SB = dict()
    PE = dict()
    for x in range(0, params['cols']):
        for y in range(0, params['rows']):
            PE[(x, y)] = dict()
            for side in params['sides']:
                ports = [Port(x, y) for t in range(0, params['num_tracks'][(x, y, BUS)])]
                SB[(x, y, side, 'in')] = ports

    sources = params['sources' + BUS]

    # add inputs from the edges as sources
    for y in range(0, params['rows']):
        # for x = 0 and all y
        for t in range(0, params['num_tracks'][(0, y, BUS)]):
            sources[(0, y, t)] = SB[(0, y, Side.W, 'in')]

        # for x = cols-1 and all y
        for t in range(0, params['num_tracks'][(params['cols'] - 1, y, BUS)]):
            sources[(params['cols'], y, t)] = SB[(params['cols'] - 1, y, Side.E, 'in')]

    for x in range(0, params['cols']):
        # for y = 0 and all x
        for t in range(0, params['num_tracks'][(x, 0, BUS)]):
            sources[(x, 0, t)] = SB[(x, 0, Side.N, 'in')]

        # for y = rows-1 and all x
        for t in range(0, params['num_tracks'][(x, params['rows'] - 1, BUS)]):
            sources[(x, params['rows'], t)] = SB[(x, params['rows'] - 1, Side.S, 'in')]

    return SB, PE


def connect_tiles(BUS, params):
    rows = params['rows']
    cols = params['cols']
    SB = params['SB' + BUS]
    num_tracks = params['num_tracks']
    sinks = params['sinks' + BUS]
    routable = params['routable' + BUS]

    for x in range(0, cols):
        for y in range(0, rows):
            for side in params['sides']:
                # Given a location and a side, mapSide returns the
                # receiving tile location and side
                adj_x, adj_y, adj_side = mapSide(x, y, side)

                # check if that switch box exists
                if (adj_x, adj_y, adj_side, 'in') in SB:
                    # make the first SB's outputs equal to
                    # the second SB's inputs
                    # i.e. no point in having redundant ports/nodes for routing
                    common_track_number = min([num_tracks[(x, y, BUS)], num_tracks[(adj_x, adj_y, BUS)]])
                    SB[(x, y, side, 'out')] = SB[(adj_x, adj_y, adj_side, 'in')][0:common_track_number]
                    # add these ports to routable
                    for t in range(0, common_track_number):
                        routable[(adj_x, adj_y, adj_side)] = SB[(adj_x, adj_y, adj_side, 'in')][t]
                # otherwise make ports for off the edge
                else:
                    ports = []
                    for t in range(0, num_tracks[(x, y, BUS)]):
                        p = Port(x, y)
                        ports.append(p)
                        sinks[(x, y, t)] = p

                    SB[(x, y, side, 'out')] = ports

    return True


def connect_pe(root, BUS, params):
    PE = params['PE' + BUS]
    SB = params['SB' + BUS]
    tracks = params['tracks' + BUS]
    sinks = params['sinks' + BUS]
    sources = params['sources' + BUS]
    for tile in root:
        y = int(tile.get('row'))
        x = int(tile.get('col'))
        # Hacky! Hardcoding the PE output port
        port = Port(x, y)
        PE[(x, y, 'out')] = port
        sources[(x, y, 'out')] = port
        for cb in tile.findall('cb'):
            if cb.get('bus') == BUS:
                for mux in cb.findall('mux'):
                    snk = mux.get('snk')
                    port = Port(x, y)
                    PE[(x, y, snk)] = port
                    sinks[(x, y, snk)] = port
                    for src in mux.findall('src'):
                        port_name = src.text
                        direc, bus, side, track = parse_name(port_name)
                        srcport = SB[(x, y, side, direc)][track]
                        dstport = PE[(x, y, snk)]  # same port that was created above
                        wire_names = (port_name, snk)
                        tracks.append(Track(srcport, dstport, wire_names, 'CB'))

    return True


def connect_sb(root, BUS, params):
    SB = params['SB' + BUS]
    PE = params['PE' + BUS]
    tracks = params['tracks' + BUS]
    for tile in root:
        x = int(tile.get('row'))
        y = int(tile.get('col'))
        for sb in tile.findall('sb'):
            if sb.get('bus') == BUS:
                for mux in sb.findall('mux'):
                    snk_name = mux.get('snk')
                    snk_direc, _, snk_side, snk_track = parse_name(snk_name)
                    for src in mux.findall('src'):
                        port_name = src.text
                        wire_names = (port_name, snk_name)
                        dstport = SB[(x, y, snk_side, snk_direc)][snk_track]
                        # input is from PE
                        if port_name[0:2] == 'pe':
                            srcport = PE[(x, y, 'out')]
                            tracks.append(Track(srcport, dstport, wire_names, 'SB'))
                        # input is from another side of the SB
                        else:
                            src_direc, _, src_side, src_track = parse_name(port_name)
                            srcport = SB[(x, y, src_side, src_direc)][src_track]
                            tracks.append(Track(srcport, dstport, wire_names, 'SB'))
                # now connect feedthroughs
                for ft in sb.findall('ft'):
                    snk_name = ft.get('snk')
                    # since it's a feedthrough, there should be exactly one source
                    src_name = ft.find('src').text
                    snk_direc, _, snk_side, snk_track = parse_name(snk_name)
                    src_direc, _, src_side, src_track = parse_name(src_name)
                    wire_names = (src_name, snk_name)
                    srcport = SB[(x, y, src_side, src_direc)][src_track]
                    dstport = SB[(x, y, snk_side, snk_direc)][snk_track]
                    tracks.append(Track(srcport, dstport, wire_names, 'SB'))

    return True
