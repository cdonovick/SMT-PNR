from util import namedtuple_with_defaults
from enum import Enum
import re

'''
   Functions to be used in fabric.py
'''

# useful custom types
muxindex = namedtuple_with_defaults('muxindex', 'resource ps po bw track port')
trackindex = namedtuple_with_defaults('trackindex', 'snk src bw')


# note using a class instead of named tuple for mutability reasons
class port_names_container:
    '''
       Lightweight class for holding port names
    '''
    def __init__(self):
        self._sinks = set()
        self._sources = set()

    @property
    def sinks(self):
        return self._sinks

    @property
    def sources(self):
        return self._sources


# note: using  class because it's more convenient if it's mutable
# unlike a namedtuple
class port_wrapper:
    '''
       Lightweight class for holding ports
       If the port is split, then source and sink will be different
       Otherwise they are exactly the same
    '''
    def __init__(self, source=None, sink=None):
        if source is None or sink is None:
            if source:
                sink = source
            elif sink:
                source = sink
            else:
                raise ValueError('Expecting at least one valid input')

            self._source = source
            self._sink = sink

    @property
    def source(self):
        return self._source

    @source.setter
    def source(self, value):
        self._source = value

    @property
    def sink(self):
        return self._sink

    @sink.setter
    def sink(self, value):
        self._sink = value


class Side(Enum):
    N = 3
    S = 1
    E = 0
    W = 2


# maps to opposite side
SideMap = {'0': Side.W, '1': Side.N, '2': Side.E, '3': Side.S}


def pos_to_side(ps, po, direc='o'):
    '''
       Takes pself and pother and returns the side from output, 'o'
       or input, 'i' perspective
    '''
    if direc == 'i':
        # switch pself and pother
        temp = po
        po = ps
        ps = temp

    delx = ps[0] - po[0]
    dely = ps[1] - po[1]

    # there should only be a change of 1 in L1 norm
    assert abs(delx) + abs(dely) == 1

    x2side = {-1: Side.E, 1: Side.W}
    y2side = {-1: Side.S, 1: Side.N}

    if delx in x2side:
        return x2side[delx]
    else:
        return y2side[dely]


def mapSide(x, y, side):
    '''
       Given a location and a side, returns the receiving tile location and receiving side
    '''
    if side is Side.N:
        return x, y-1, Side.S
    elif side is Side.S:
        return x, y+1, Side.N
    elif side is Side.E:
        return x+1, y, Side.W
    elif side is Side.W:
        return x-1, y, Side.E
    else:
        raise ValueError('Expected a Side but got {}'.format(type(side)))


def get_sb_params(ps, text, direc='o'):
    '''
       Takes an x, y and port name and returns
       po: position of other (receiving) tile
       track: the track number
       bw: bus width

       direc: only changes for internal memory tiles
       direc = 'o': (x, y) sb_wire_out_1_BUS16_3_0 ---> (x, y-1)
       direc = 'i': (x, y) sb_wire_out_1_BUS16_3_0 ---> (x, y+1)
    '''
    x = ps[0]
    y = ps[1]

    p = re.compile(r'(?P<mem_int>sb_wire_)?'
                   '(?:in|out)(?:_\d*)?_'
                   'BUS(?P<bus>\d+)_'
                   'S?(?P<side>\d+)_'
                   'T?(?P<track>\d+)')
    m = p.search(text)

    _side = Side(int(m.group('side')))
    _track = int(m.group('track'))
    _bus = int(m.group('bus'))

    if m.group('mem_int'):
        # internal memory wires have non-standard sides
        # need to do a mapping, overwriting _side
        _, b, _side, t = parse_mem_sb_wire(text, direc)
        # everything except for the side should stay the same
        assert b == 'BUS' + str(_bus)
        assert int(t) == _track

    xn, yn, _ = mapSide(x, y, _side)

    return (xn, yn), _bus, _track, _side


def parse_name(text):
    '''
        Takes a (non-PE) port name and returns direction, BUS width, side, track number
    '''
    s = text.split('_')
    return s[0], s[1], Side(int(s[2][1])), int(s[3][1])


def parse_mem_sb_wire(text, direc='o'):
    '''
       Takes an internal memory tile wire, with prefix sb_wire and parses it
       Returns direc, bus_width, side, track
    '''

    # decide which one to reverse
    if direc == 'o':
        dselect = {'out': True, 'in': False}
    else:
        dselect = {'out': False, 'in': True}

    s = text.split('_')
    if dselect[s[2]]:
        return s[2], s[4], Side(int(s[5])), int(s[6])
    else:
        # side is backwards
        return s[2], s[4], SideMap[s[5]], int(s[6])
