from util import NamedIDObject, IDObject
from .fabricutils import Side
from .fabricutils import pos_to_side
from design.module import Resource


class Port(IDObject):
    '''
       Represents a port on a fabric
       x         : x coordinate
       y         : y coordinate
       resource  : Side enum for regular tracks. Resource enum for CB ports
       track     : track number (or port name for PE)
       direction : in or out (i or o)
    '''
    def __init__(self, muxindex, direction='o'):
        super().__init__()
        # see fabricutils for muxindex documentation
        if muxindex.resource == Resource.SB:
            # easier to look at side for naming
            res = pos_to_side(muxindex.ps, muxindex.po, direction)
        else:
            res = muxindex.resource

        # naming scheme is (x, y)Side_direction[track]
        self.name = '({}, {}){}_{}[{}]'.format(muxindex.ps[0],
                                               muxindex.ps[1],
                                               res.name,
                                               direction,
                                               muxindex.track if muxindex.track is not None
                                               else muxindex.port)
        self._x = muxindex.ps[0]
        self._y = muxindex.ps[1]
        self._resource = res
        self._track = muxindex.track  # could be none
        self._track = track
        self._inputs = set()
        self._outputs = set()
        self._index = muxindex

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @property
    def side(self):
        '''
           Returns the resource assuming it's a side
        '''
        assert self._resource.name in Side.__members__
        return self._resource

    @property
    def resource(self):
        return self._resource

    @property
    def index(self):
        return self._index

    @property
    def track(self):
        return self._track

    @property
    def inputs(self):
        return self._inputs

    @property
    def outputs(self):
        return self._outputs

    @property
    def track(self):
        return self._track

    @property
    def inputs(self):
        return self._inputs

    @property
    def outputs(self):
        return self._outputs

    @property
    def loc(self):
        return (self._x, self._y)

    def split(self):
        snkport = Port(self._index)
        snkport._inputs = self._inputs
        for track in snkport._inputs:
            track._dst = snkport

        srcport = Port(self._index, 'i')
        # overwrite x, y and name
        srcport._x = self._index.po[0]
        srcport._y = self._index.po[1]
        # reverse positions
        s = pos_to_side(self._index.po, self._index.ps)
        # make the name look right/nice for printout
        srcport.name = '({}, {}){}_{}[{}]'.format(srcport._x,
                                                  srcport._y,
                                                  s.name,
                                                  'i',
                                                  self._index.track if self._index.track is not None
                                                  else self._index.port)
        srcport._outputs = self._outputs
        for track in srcport._outputs:
            track._src = srcport
        return snkport, srcport

    def __repr__(self):
        return self.name


class Track(NamedIDObject):
    '''
       Holds two ports describing a single track between them
       Note: only ports for inputs are described (except for ports off the edge)
             This is because output ports always map to the same input port of
             neighboring tiles thus its redundant to have both (and unnecessarily
             inflates the graph)
    '''
    def __init__(self, src, dst, width):
        super().__init__('{}-{}->{}'.format(src, width, dst))
        self._src = src
        self._dst = dst
        self._src.outputs.add(self)
        self._dst.inputs.add(self)
        self._width = width

    @property
    def src(self):
        return self._src

    @property
    def dst(self):
        return self._dst

    @property
    def width(self):
        return self._width

    # overload repr, because tracks may change when splitting ports
    def __repr__(self):
        return '{}-{}->{}'.format(self.src, self.width, self.dst)


class Fabric:
    def __init__(self, parsed_params):
        self._rows = parsed_params['rows']
        self._cols = parsed_params['cols']
        self._num_tracks = min(parsed_params['num_tracks'].values())
        self._locations = parsed_params['locations']
        # temporarily limiting register locations
        if Resource.Reg in self._locations:
            self._locations[Resource.Reg] = self._locations[Resource.Reg] - \
                                            self._locations[Resource.Mem]
        self._config = parsed_params['config_engine']
        self._fab = parsed_params['fabric']
        self._port_names = parsed_params['port_names']

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
    def num_tracks(self):
        return self._num_tracks

    @property
    def port_names(self):
        return self._port_names

    @property
    def locations(self):
        '''
            Returns a dictionary of resource type --> set of locations
        '''
        return self._locations

    # hacky returns all x==0 or y==0 locations for ios
    @property
    def io_locations(self):
        locs = set()
        for y in range(0, self.rows):
            locs.add((0, y))
        for x in range(0, self.cols):
            locs.add((x, 0))

        return locs

    def __getitem__(self, index):
        return self._fab[index]

    @property
    def config(self):
        return self._config

    def matching_keys(self, named_tuple_key):
        return self._fab._getmatching(named_tuple_key)
