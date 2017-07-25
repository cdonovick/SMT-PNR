import xml.etree.ElementTree as ET
from fabric.fabricutils import Side, mapSide, parse_mem_sb_wire
from fabric.fabricutils import muxindex, trackindex, port_wrapper, port_names_container
from design.module import Resource
from fabric import Port, Track, Fabric
from util import SelectDict
from config import config, configindex
from collections import defaultdict
import re

__all__ = ['parse_xml']

SB = Resource.SB
CB = Resource.CB

resourcedict = {'pe_tile_new': Resource.PE,
                'memory_tile': Resource.Mem,
                'pe': Resource.PE,
                'mem': Resource.Mem}


def parse_xml(filepath, config_engine):

    tree = ET.parse(filepath)
    root = tree.getroot()

    params = dict()
    params['config_engine'] = config_engine
    params['fabric'] = dict()
    _scan_ports(root, params)
    _connect_ports(root, params)

    # overwrite dicts with SelectDicts
    params['fabric'] = SelectDict(params['fabric'])
    fab = Fabric(params)
    config_engine.fabric = fab
    return fab


def _scan_ports(root, params):

    '''
       Reads the fabric xml in a first pass, recording all muxes and 
       determining useful parameters like rows/cols
    '''

    # make sure indexing is correct and that
    # you never get the same index twice when
    # scanning ports
    sanitycheckset = set()

    fabric = params['fabric']
    locations = defaultdict(set)
    params['locations'] = locations

    num_tracks = dict()
    params['num_tracks'] = num_tracks
    config_engine = params['config_engine']

    # port_names are
    # {(resource, layer) : port_names_container}
    port_names = defaultdict(port_names_container)
    params['port_names'] = port_names

    rows = 0
    cols = 0

    def _scan_sb(sb):
        # memory tiles have multiple rows of switch boxes
        if sb.get('row'):
            _ps = (x, y + int(sb.get("row")))
        else:
            _ps = (x, y)

        for mux in sb.findall('mux'):
            mindex = _get_index(_ps, mux.get('snk'), _resource)

            assert mindex not in sanitycheckset
            sanitycheckset.add(mindex)
            fabric[mindex] = port_wrapper(Port(mindex))

        # TODO: Handle feedthroughs -- should be simple

    def _scan_cb(cb):
        _bw = int(cb.get('bus').replace('BUS', ''))
        _ps = (x, y)
        for mux in cb.findall('mux'):
            _port = mux.get('snk')
            # add to sinks
            port_names[(_resource, _bw)].sinks.add(_port)
            mindex = _get_index(_ps, _port, _resource, bw=_bw)
            # debugging
            assert mindex == muxindex(resource=_resource, ps=_ps, bw=_bw, port=_port)
            fabric[mindex] = port_wrapper(Port(mindex))

    def _scan_resource(res):
        # TODO: handle attributes
        d = dict()
        d['feature_address'] = int(res.get('feature_address'))
        for tag in res:
            if not isinstance(tag.tag, str):
                # skip comments in the xml
                continue

            try:
                dv = int(tag.text)
            except Exception:
                dv = tag.text

            tag_d = {'val': dv}

            for k, v in tag.items():
                try:
                    v = int(v)
                except Exception:
                    pass

                # for memories, standardize bit to bith/bitl
                if k == 'bit':
                    tag_d['bith'] = v
                    tag_d['bitl'] = v

                else:
                    tag_d[k] = v

            if len(tag.keys()) > 0:
                d[tag.tag] = config(tag_d)
            else:
                d[tag.tag] = dv

        ci = configindex(ps=(x, y), resource=resourcedict[res.tag])
        config_engine[ci] = config(d)

    fabelements = {'sb': _scan_sb,
                   'cb': _scan_cb,
                   'pe': _scan_resource,
                   'mem': _scan_resource}

    for tile in root:
        if tile.get("type"):
            _resource = resourcedict[tile.get("type")]
        else:
            _resource = Resource.PE

        x = int(tile.get('col'))
        y = int(tile.get('row'))
        # note, memory tiles will add the sb row to y

        if x > cols:
            cols = x

        if y > rows:
            rows = y

        # add to the set of locations for that resource
        locations[_resource].add((x, y))

        # get the number of tracks
        trackparams = tile.get('tracks').split()
        for t in trackparams:
            tr = t.split(':')
            bw = int(tr[0].replace('BUS', ''))
            num_tracks[(x, y, bw)] = int(tr[1])

        for element, processor in fabelements.items():
            for tag in tile.findall(element):
                processor(tag)

    # want the number of rows not the value
    # i.e. 0-7 means 8
    params['rows'] = rows + 1
    params['cols'] = cols + 1


def _connect_ports(root, params):

    # make sure indexing is correct and that
    # you never get the same index twice when
    # scanning ports
    tracksanitycheckset = set()

    fabric = params['fabric']
    locations = params['locations']
    port_names = params['port_names']
    config_engine = params['config_engine']

    def _connect_sb(sb):
        # memory tiles have multiple rows of switch boxes
        if sb.get('row'):
            _ps = (x, y + int(sb.get("row")))
        else:
            _ps = (x, y)

        tile_addr = int(tile.get('tile_addr'))
        tile_type = tile.get('type')

        config_engine[_ps] = config(tile_addr=tile_addr,
                                    tile_type=tile_type)

        fa = int(sb.get('feature_address'))
        sel_w = int(sb.find('sel_width').text)

        for mux in sb.findall("mux"):
            snk_name = mux.get('snk')
            snkindex = _get_index(_ps, snk_name, _resource)

            ch = int(mux.get('configh'))
            cl = int(mux.get('configl'))

            if mux.get('reg') == '1':
                locations[Resource.Reg].add(_ps + (snkindex.track,))
                assert int(mux.get('configr')) is not None, mux.get('configr')
                cr = int(mux.get('configr'))
            else:
                cr = None

            for src in mux.findall('src'):
                src_name = src.text
                srcindex = _get_index(_ps, src_name, _resource, 'i', snkindex.bw, y)

                sel = int(src.get('sel'))

                # handle ports off the edge
                if srcindex not in fabric:
                    fabric[srcindex] = port_wrapper(Port(srcindex, 'i'))

                    # add to sources if it has a port name
                    if srcindex.port is not None:
                        assert srcindex.resource != SB
                        port_names[(srcindex.resource, snkindex.bw)].sources.add(srcindex.port)

                assert srcindex.bw == snkindex.bw, \
                    'Attempting to connect ports with different bus widths'

                # see fabric.fabricutils for trackindex documentation
                tindex = trackindex(snk=snkindex, src=srcindex, bw=srcindex.bw)
                assert tindex not in tracksanitycheckset
                tracksanitycheckset.add(tindex)
                track = Track(fabric[srcindex].source, fabric[snkindex].sink, srcindex.bw)
                fabric[tindex] = track
                config_engine[tindex] = config(feature_address=fa, sel_w=sel_w, configh=ch,
                                               configl=cl, configr=cr, sel=sel,
                                               src_name=src_name, snk_name=snk_name)

    def _connect_cb(cb):
        _bw = int(cb.get('bus').replace('BUS', ''))
        _ps = (x, y)

        fa = int(cb.get('feature_address'))
        sel_w = int(cb.find('sel_width').text)

        for mux in cb.findall("mux"):
            _port = mux.get('snk')
            snkindex = _get_index(_ps, _port, _resource, bw=_bw)

            for src in mux.findall("src"):
                sel = int(src.get('sel'))
                src_name = src.text
                srcindex = _get_index(_ps, src_name, _resource, 'i', _bw)

                # handle ports off the edge
                if srcindex not in fabric:
                    fabric[srcindex] = port_wrapper(Port(srcindex, 'i'))

                assert srcindex.bw == snkindex.bw, \
                    'Attempting to connect ports with different bus widths'

                tindex = trackindex(snk=snkindex, src=srcindex, bw=srcindex.bw)
                assert tindex not in tracksanitycheckset
                tracksanitycheckset.add(tindex)

                track = Track(fabric[srcindex].source, fabric[snkindex].sink, _bw)
                fabric[tindex] = track
#                track_names = (src_name, _port)
                config_engine[tindex] = config(feature_address=fa, sel_w=sel_w, sel=sel,
                                               src_name=src_name, snk_name=_port)

    elem2connector = {'sb': _connect_sb,
                      'cb': _connect_cb}

    for tile in root:
        x = int(tile.get('col'))
        y = int(tile.get('row'))
        # note, memory tiles will add the sb row to y

        if tile.get("type"):
            _resource = resourcedict[tile.get("type")]
        else:
            _resource = Resource.PE

        for elem, connector in elem2connector.items():
            for tag in tile.findall(elem):
                connector(tag)


# Helper Functions
def _get_index(ps, name, resource, direc='o', bw=None, tile_y=None):
    # note: sometimes need to pass bus width because can't be inferred from name
    # e.g. pe_out_res
    # also use for some sanity checks -- there will be redundancy occasionally

    x = ps[0]
    y = ps[1]

    p = re.compile(r'(?P<mem_int>sb_wire_)'
                   '?(?:in|out)(?:_\d*)?_'
                   'BUS(?P<bus>\d+)_'
                   'S?(?P<side>\d+)_'
                   'T?(?P<track>\d+)')

    m = p.search(name)

    # see fabric.fabricutils for muxindex documentation

    if not m:
        if resource == Resource.Mem and direc == 'i':
            # special case for memory tile output
            # want to make sure referring to same port even from switch
            # boxes of different rows
            assert tile_y is not None
            return muxindex(resource=resource, ps=(ps[0], tile_y), bw=bw, port=name)
        else:
            return muxindex(resource=resource, ps=ps, bw=bw, port=name)
    else:
        _side = Side(int(m.group('side')))
        _track = int(m.group('track'))
        _bus = int(m.group('bus'))

        if bw is not None:
            assert _bus == bw, 'Expected bus width to be '
            '{} but it is {}'.format(bw, _bus)

        if m.group('mem_int'):
            # internal memory wires have non-standard sides
            # need to do a mapping, overwriting _side
            _, b, _side, t = parse_mem_sb_wire(name, direc)
            # everything except for the side should stay the same
            assert b == 'BUS' + str(_bus)
            assert int(t) == _track

        xn, yn, _ = mapSide(x, y, _side)

        if direc == 'o':
            return muxindex(resource=SB, ps=ps, po=(xn, yn), bw=_bus, track=_track)
        else:
            # pself and pother swapped for in wires
            return muxindex(resource=SB, ps=(xn, yn), po=ps, bw=_bus, track=_track)
