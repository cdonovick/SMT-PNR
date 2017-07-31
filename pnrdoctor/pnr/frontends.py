from collections import defaultdict
import re
import xml.etree.ElementTree as ET


from pnrdoctor.config import config
from pnrdoctor.design.module import Resource
from pnrdoctor.fabric.fabricutils import Side, mapSide, parse_mem_sb_wire
from pnrdoctor.fabric.fabricutils import muxindex, trackindex, port_wrapper, port_names_container
from pnrdoctor.fabric import Port, Track, Fabric
from pnrdoctor.util import SelectDict
from .pnrutils import configindex

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

    # keep track of feedthrough information in a generic object with settable attributes
    ftdata = lambda: 0
    # keep feedthrough paths separate until the whole path is built up
    ftdata.muxindices = set()
    # {port -> set of ports} temporary storage for building paths
    ftdata.muxindex2paths = dict()
    # {set of ports --> (port1, port2)} maps from set representing a path to terminal ports
    # the terminal ports should be included in the fabric
    # but intermediate ports in a feedthrough path are never added to the fabric
    ftdata.terminals = dict()


    params['ftdata'] = ftdata

    fabric = params['fabric']
    locations = defaultdict(set)
    params['locations'] = locations
    muxindex_locations = defaultdict(set)
    params['muxindex_locations'] = muxindex_locations

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

            if mux.get('reg') == '1':
                # add to register muxindex_locations
                muxindex_locations[Resource.Reg].add(mindex)

            assert mindex not in sanitycheckset
            sanitycheckset.add(mindex)
            fabric[mindex] = port_wrapper(Port(mindex))

        # Scan feedthrough ports
        for ft in sb.findall('ft'):
            mindex = _get_index(_ps, ft.get('snk'), _resource)
            assert mindex not in ftdata.muxindices
            ftdata.muxindices.add(mindex)


    def _scan_cb(cb):
        _bw = int(cb.get('bus').replace('BUS', ''))
        _ps = (x, y)
        for mux in cb.findall('mux'):
            _port = mux.get('snk')
            # add to sinks
            port_names[(_resource, _bw)].sinks.add(_port)
            mindex = _get_index(_ps, _port, _resource, bw=_bw)
            # add to muxindex_locations
            muxindex_locations[_resource].add(mindex)

            # sanity check
            assert mindex == muxindex(resource=_resource, ps=_ps,
                                      bw=_bw, port=_port), \
                                      'mismatch in get_index and expected index'
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
    pathsanitycheckset = set()

    fabric = params['fabric']
    locations = params['locations']
    port_names = params['port_names']
    config_engine = params['config_engine']
    ftdata = params['ftdata']
    muxindex_locations = params['muxindex_locations']

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
                # but if it's a nonterminal feedthrough port, do nothing
                if srcindex not in fabric and srcindex not in ftdata.muxindices:
                    fabric[srcindex] = port_wrapper(Port(srcindex, 'i'))

                    # add to sources if it has a port name
                    if srcindex.port is not None:
                        assert srcindex.resource != SB
                        port_names[(srcindex.resource, snkindex.bw)].sources.add(srcindex.port)
                        muxindex_locations[srcindex.resource].add(srcindex)

                assert srcindex.bw == snkindex.bw, \
                    'Attempting to connect ports with different bus widths'

                # if it connects to a feedthrough, don't make the connection yet. Want only one
                # track connecting endpoints of feedthrough path

                if srcindex not in ftdata.muxindices:
                    # see fabric.fabricutils for pathindex documentation
                    pindex = pathindex(snk=snkindex, src=srcindex, bw=srcindex.bw)
                    assert pindex not in pathsanitycheckset
                    pathsanitycheckset.add(pindex)
                    track = Track(fabric[srcindex].source, fabric[snkindex].sink, srcindex.bw)
                    fabric[pindex] = track
                    config_engine[pindex] = config(feature_address=fa, sel_w=sel_w, configh=ch,
                                                   configl=cl, configr=cr, sel=sel,
                                                   src_name=src_name, snk_name=snk_name)

        # connect feed throughs
        for ft in sb.findall('ft'):
            snk_name = ft.get('snk')
            snkindex = _get_index(_ps, snk_name, _resource)

            # ch = int(ft.get('configh'))
            # cl = int(ft.get('configl'))

            assert len(ft.findall('src')) == 1, 'Feedthroughs should have exactly one source'
            for src in ft.findall('src'):
                src_name = src.text
                srcindex = _get_index(_ps, src_name, _resource, 'i', snkindex.bw, y)

#                sel = int(src.get('sel'))

                # handle ports off the edge
                if srcindex not in fabric and srcindex not in ftdata.muxindices:
                    fabric[srcindex] = port_wrapper(Port(srcindex, 'i'))
                    muxindex_locations[srcindex.resource].add(srcindex)

                assert srcindex.bw == snkindex.bw, \
                  'Attempting to connect ports with different bust widths'

                pindex = pathindex(snk=snkindex, src=srcindex, bw=srcindex.bw)
                assert pindex not in pathsanitycheckset
                pathsanitycheckset.add(pindex)

                config_engine[pindex] = config(feature_address=fa, sel_w=sel_w, configh=ch,
                                               configl=cl, configr=cr, sel=sel,
                                               src_name=src_name, snk_name=snk_name)

                for mindex in {srcindex, snkindex}:
                    if mindex not in ftdata.muxindex2paths:
                        ftdata.muxindex2paths[mindex] = (pindex,)

                # take union of sets to add to the same path
                oldsrcpath = ftdata.muxindex2paths[srcindex]
                oldsnkpath = ftdata.muxindex2paths[snkindex]

                for path in {oldsrcpath, oldsnkpath}:
                    if path not in ftdata.terminals:
                        ftdata.terminals[path] = dict()

                newpath = oldsrcpath + oldsnkpath
                ftdata.muxindex2paths[srcindex] = newpath
                ftdata.muxindex2paths[snkindex] = newpath

                # if mindex is in fabric then it must be a terminal port of the feedthrough path
                if srcindex in fabric:
                    ftdata.terminals[oldsrcpath]['H'] = srcindex

                if snkindex in fabric:
                    ftdata.terminals[oldsnkpath]['T'] = snkindex

                # update terminals
                assert set(ftdata.terminals[oldsrcpath].keys()) != \
                       set(ftdata.terminals[oldsnkpath].keys()) or \
                       oldsrcpath == oldsnkpath, \
                       'There should never be more than one Head or Tail for a path'

                ftdata.terminals[newpath] = ftdata.terminals[oldsrcpath].copy()
                ftdata.terminals[newpath].update(ftdata.terminals[oldsnkpath])

                # delete old references
                del ftdata.terminals[oldsrcpath]
                if oldsrcpath != oldsnkpath:
                    del ftdata.terminals[oldsnkpath]


    for path, terminals in ftdata.terminals:
        pindex = pathindex(src=terminals['H'], snk=terminals['T'], bw=next(iter(path)).bw)

        fabric[pindex] = Track(fabric[pindex.src].source, fabric[pindex.snk].sink, pindex.bw)
        # maybe don't need to keep track of intermediate tracks
        # fabric[pindex] = FeedthroughPath(fabric[pindex.src].source, fabric[pindex.snk].sink,
        #                                  pindex.bw, path)



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

                pindex = pathindex(snk=snkindex, src=srcindex, bw=srcindex.bw)
                assert pindex not in pathsanitycheckset
                pathsanitycheckset.add(pindex)

                track = Track(fabric[srcindex].source, fabric[snkindex].sink, _bw)
                fabric[pindex] = track
#                track_names = (src_name, _port)
                config_engine[pindex] = config(feature_address=fa, sel_w=sel_w, sel=sel,
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
            return muxindex(resource=Resource.SB, ps=ps, po=(xn, yn), bw=_bus, track=_track)
        else:
            # pself and pother swapped for in wires
            return muxindex(resource=Resource.SB, ps=(xn, yn), po=ps, bw=_bus, track=_track)
