
from collections import defaultdict
import re
import xml.etree.ElementTree as ET
import json

from pnrdoctor.config import config
from pnrdoctor.design.module import Resource, Layer
from pnrdoctor.fabric.fabricutils import Side, mapSide, parse_mem_sb_wire, pos_to_side
from pnrdoctor.fabric.fabricutils import muxindex, trackindex, port_wrapper, port_names_container
from pnrdoctor.fabric import Port, Track, Fabric
from pnrdoctor.util import SelectDict, STAR, BiMultiDict
from .pnrutils import configindex
from pnrdoctor.design.core2graph import _PORT_TRANSLATION

__all__ = ['parse_xml', 'parse_board_info']

SB = Resource.SB
CB = Resource.CB

resourcedict = {'pe_tile_new': Resource.PE,
                'memory_tile': Resource.Mem,
                'pe': Resource.PE,
                'mem': Resource.Mem,
                'io1bit': Resource.IO,
                'io16bit': Resource.IO,
                'empty': Resource.EMPTY}

# The only types of tiles which can be bypassed
# i.e. 1 bit IO tile tracks can skip over these
bypass_resources = {Resource.IO, Resource.EMPTY}
ioempty_positions = set()

# HACK
ignore_types = {"gst"}

def widths2layer(w):
    if w == {1, 16}:
        return Layer.Combined
    elif w == {16}:
        return Layer.Data
    elif w == {1}:
        return Layer.Bit
    else:
        raise RuntimeError("Unhandled width={}".format(w))

def parse_xml(filepath, config_engine):

    tree = ET.parse(filepath)
    root = tree.getroot()

    params = dict()
    params['config_engine'] = config_engine
    params['fabric'] = dict()
    _scan_ports(root, params)
    _connect_ports(root, params)

    # replace with a SelectDict
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
    processed_muxes = set()

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

    io_groups = defaultdict(list)
    params['io_groups'] = io_groups

    numrows = 0
    numcols = 0
    params['layers'] = set()

    def _proc_io(io_tile):
        _ps = (row, col)
        tile_addr = int(tile.get("tile_addr"), 0)
        tile_type = tile.get("type")
        config_engine[_ps] = config(tile_addr=tile_addr,
                                    tile_type=tile_type)

        name = io_tile.get("name")

        io_bit = None
        if tile_type == "io1bit":
            layer = Layer.Bit
            io_bit = int(io_tile.find("io_bit").text, 0)
        else:
            layer = Layer.Data

        input_name = tile.find('input').text
        input_index = _get_index((row, col), input_name, Resource.IO)
        fabric[input_index]  = port_wrapper(Port(input_index))

        for o in tile.findall('output'):
            output_name = o.text
            output_index = _get_index((row, col), output_name, Resource.IO)
            fabric[output_index] = port_wrapper(Port(output_index, 'i'))

        ig = int(tile.find("io_group").text, 0)
        io_groups[(ig, layer)].append(_ps)
        tri = tile.find("tri")
        tri_dict = {"feature_address": int(tri.get("feature_address"), 0),
                    "reg_address": int(tri.get("reg_address"), 0),
                    "bith": int(tri.get("bith"), 0),
                    "bitl": int(tri.get("bitl"), 0)}
        directions = {}
        for d in tri.findall("direction"):
            sel = int(d.get("sel"))
            directions[d.text] = sel
        tri_dict["direction"] = config(directions)

        # create config index
        ci = configindex(ps=_ps, resource=Resource.IO)

        # get mux info from 1 bit
        if layer == Layer.Bit:
            mux = tile.find("mux")
            mux_dict = {"feature_address": int(mux.get("feature_address"), 0),
                        "reg_address": int(mux.get("reg_address"), 0),
                        "bith": int(mux.get('bith'), 0),
                        "bitl": int(mux.get('bitl'), 0)}
            srcs = {}
            for s in mux.findall('src'):
                srcs[Layer.width_to_layer(int(s.text))] = int(s.get('sel'), 0)
            mux_dict['sel'] = srcs

            config_engine[ci] = config(io_group=ig, tri=config(tri_dict),
                                       mux=config(mux_dict), name=name, io_bit=io_bit)
        else:
            config_engine[ci] = config(io_group=ig, tri=config(tri_dict), name=name)

    def _scan_sb(sb):
        # memory tiles have multiple rows of switch boxes
        if sb.get('row'):
            _ps = (row + int(sb.get("row"), 0), col)
        else:
            _ps = (row, col)

        for mux in sb.findall('mux'):

            mindex = _get_index(_ps, mux.get('snk'), _resource)

            if mindex not in processed_muxes:
                processed_muxes.add(mindex)
                fabric[mindex] = port_wrapper(Port(mindex))

        # Scan feedthrough ports
        for ft in sb.findall('ft'):
            mindex = _get_index(_ps, ft.get('snk'), _resource)
            assert mindex not in ftdata.muxindices
            ftdata.muxindices.add(mindex)


    def _scan_cb(cb):
        _bw = int(cb.get('bus').replace('BUS', ''), 0)
        _ps = (row, col)

        params['layers'].add(_bw)

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
        def _try_int(v):
            try:
                return int(v, 0)
            except:
                return v

        # TODO: handle attributes
        d = dict()
        d['feature_address'] = int(res.get('feature_address'), 0)

        counts = dict()
        for tag in res:
            if not isinstance(tag.tag, str):
                # skip comments in the xml
                continue

            if tag.tag not in counts:
                counts[tag.tag] = len(res.findall(tag.tag))

            try:
                dv = int(tag.text, 0)
            except Exception:
                dv = tag.text.strip()

            tag_d = dict()

            for k, v in tag.items():
                v = _try_int(v)

                # for memories, standardize bit to bith/bitl
                if k == 'bit':
                    tag_d['bith'] = v
                    tag_d['bitl'] = v

                else:
                    tag_d[k] = v

            # This is intended for opcodes and muxes but works with anything following the same pattern
            # <repeated tag: useful attributes> unique str </repeated tag>
            for t in tag:
                if not dv:
                    # mux uses snk as key
                    if tag.get('snk'):
                        dv = tag.get('snk')
                    # opcode uses tag name, "op", as key
                    else:
                        dv = t.tag
                # opcodes use name attribute
                if t.get("name"):
                    key = t.get("name")
                else:
                    key = t.text
                tag_d[key] = config({k: _try_int(v) for k, v in t.items()})

            # when there are multiple tags, differentiate with text content
            if counts[tag.tag] > 1:
                if tag.tag not in d:
                    d[tag.tag] = dict()
                if dv:
                    assert isinstance(dv, str), dv
                    assert dv not in d[tag.tag]
                    assert len(tag_d) > 0, "Need some kind of data"
                    d[tag.tag][dv] = config(tag_d)
            else:
                if dv:
                    tag_d['val'] = dv
                if len(tag.keys()) > 1:
                    data = config(tag_d)
                else:
                    data = dv
                d[tag.tag] = data

        for k in d:
            if isinstance(d[k], dict):
                d[k] = config(d[k])

        ci = configindex(ps=(row, col), resource=resourcedict[res.tag])
        config_engine[ci] = config(d)

    fabelements = {'sb': _scan_sb,
                   'cb': _scan_cb,
                   'pe': _scan_resource,
                   'mem': _scan_resource,
                   'empty': lambda x: 0}  # no op for empty tile

    for tile in root:
        if tile.get("type"):
            #HACK
            if tile.get("type") in ignore_types:
                continue
            _resource = resourcedict[tile.get("type")]
        else:
            _resource = Resource.PE

        col = int(tile.get('col'), 0)
        row = int(tile.get('row'), 0)
        # note, memory tiles will add the sb row to y

        if col > numcols:
            numcols = col

        if row > numrows:
            numrows = row

        bus_widths = set()
        # get the number of tracks
        trackparams = tile.get('tracks').split()
        for t in trackparams:
            tr = t.split(':')
            bw = int(tr[0].replace('BUS', ''), 0)
            count = int(tr[1], 0)
            num_tracks[(row, col, bw)] = count
            if count > 0:
                bus_widths.add(bw)

        # HACK
        if _resource == Resource.PE:
            for w in bus_widths:
                locations[_resource, Layer.width_to_layer(w)].add((row, col))
            # HACK
            if len(bus_widths) == 2:
                locations[_resource, Layer.Combined].add((row, col))
            else:
                assert False
        else:
            locations[_resource, widths2layer(bus_widths)].add((row, col))

        for element, processor in fabelements.items():
            for tag in tile.findall(element):
                processor(tag)

        if _resource == Resource.IO:
            _proc_io(tile)

        # keep track of potential bypass locations
        if _resource in bypass_resources:
            ioempty_positions.add((row, col))

    # want the number of rows not the value
    # i.e. 0-7 means 8
    params['numrows'] = numrows + 1
    params['numcols'] = numcols + 1


def _connect_ports(root, params):

    # make sure indexing is correct and that
    # you never get the same index twice when
    # scanning ports
    processed_tracks = set()

    fabric = params['fabric']
    locations = params['locations']
    port_names = params['port_names']
    config_engine = params['config_engine']
    ftdata = params['ftdata']
    muxindex_locations = params['muxindex_locations']
    io_groups = params["io_groups"]

    # needed for _infer_src
    io16_positions = list()
    for t, l in io_groups.items():
        if t[1] == Layer.Data:
            io16_positions += l

    def _connect_sb(sb):
        # memory tiles have multiple rows of switch boxes
        if sb.get('row'):
            _ps = (row + int(sb.get("row"), 0), col)
        else:
            _ps = (row, col)

        _bw = int(sb.get('bus').replace('BUS', ''), 0)

        tile_addr = int(tile.get('tile_addr'), 0)
        tile_type = tile.get('type')

        config_engine[_ps] = config(tile_addr=tile_addr,
                                    tile_type=tile_type)

        fa = int(sb.get('feature_address'), 0)
        sel_w = int(sb.find('sel_width').text, 0)

        for reg in sb.findall('reg'):
            name = reg.get('src')
            index = _get_index(_ps, name, _resource)

            bh = int(reg.get('bith'), 0)
            bl = int(reg.get('bitl'), 0)
            reg_address = int(reg.get('reg_address'), 0)
            default = int(reg.get('default'), 0)

            locations[Resource.Reg, Layer.width_to_layer(_bw)].add(_ps + (index.track,))
            # add to register muxindex_locations
            muxindex_locations[Resource.Reg].add(index)

            config_engine[index] = config(reg_address=reg_address, bith=bh, bitl=bl, default=default, name=name)

        for mux in sb.findall("mux"):
            snk_name = mux.get('snk')
            snkindex = _get_index(_ps, snk_name, _resource)
            bh = int(mux.get('bith'), 0)
            bl = int(mux.get('bitl'), 0)
            ra = int(mux.get('reg_address'), 0)

            for src in mux.findall('src'):
                src_name = src.text
                srcindex = _get_index(_ps, src_name, _resource, 'i', snkindex.bw, row)

                sel = int(src.get('sel'), 0)

                # handle ports off the edge
                # but if it's a nonterminal feedthrough port, do nothing

                if srcindex not in fabric:
                    srcindex = _infer_src(_ps, srcindex, ftdata, fabric, io16_positions)
                    # add to sources if it has a port name
                    if srcindex.port is not None:
                        assert srcindex.resource != SB
                        port_names[(srcindex.resource, snkindex.bw)].sources.add(srcindex.port)
                        muxindex_locations[srcindex.resource].add(srcindex)

                assert srcindex.bw == snkindex.bw, \
                    'Attempting to connect ports with different bus widths. {}, {}'.format(srcindex, snkindex)

                # if it connects to a feedthrough, don't make the connection yet. Want only one
                # track connecting endpoints of feedthrough path

                # see fabric.fabricutils for trackindex documentation
                tindex = _create_track(srcindex, snkindex, fabric, processed_tracks)
                config_engine[tindex] = config(feature_address=fa, sel_w=sel_w, bith=bh,
                                               bitl=bl, reg_address=ra, sel=sel,
                                               src_name=src_name, snk_name=snk_name)

        # connect feed throughs
        for ft in sb.findall('ft'):
            snk_name = ft.get('snk')
            snkindex = _get_index(_ps, snk_name, _resource)

            assert len(ft.findall('src')) == 1, 'Feedthroughs should have exactly one source'
            for src in ft.findall('src'):
                src_name = src.text
                srcindex = _get_index(_ps, src_name, _resource, 'i', snkindex.bw, row)

                # handle ports off the edge
                if srcindex not in fabric and srcindex not in ftdata.muxindices:
                    srcindex = _infer_src(_ps, srcindex, ftdata, fabric, io16_positions)
                    assert srcindex in fabric, \
                      "Should be an existing IO, or a just added off-the-edge node"

                    muxindex_locations[srcindex.resource].add(srcindex)

                assert srcindex.bw == snkindex.bw, \
                  'Attempting to connect ports with different bust widths'

                tindex = trackindex(snk=snkindex, src=srcindex, bw=srcindex.bw)
                assert tindex not in processed_tracks
                processed_tracks.add(tindex)

                for mindex in {srcindex, snkindex}:
                    if mindex not in ftdata.muxindex2paths:
                        ftdata.muxindex2paths[mindex] = (tindex,)

                # get paths
                oldsrcpath = ftdata.muxindex2paths[srcindex]
                oldsnkpath = ftdata.muxindex2paths[snkindex]

                for path in {oldsrcpath, oldsnkpath}:
                    if path not in ftdata.terminals:
                        ftdata.terminals[path] = dict()

                # take union to create new path
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

                # update the path --> terminals dict
                ftdata.terminals[newpath] = ftdata.terminals[oldsrcpath].copy()
                ftdata.terminals[newpath].update(ftdata.terminals[oldsnkpath])

                # delete old references
                del ftdata.terminals[oldsrcpath]
                if oldsrcpath != oldsnkpath:
                    del ftdata.terminals[oldsnkpath]


        for path, terminals in ftdata.terminals:
            # make path from beginning of feedthrough to end
            tindex = trackindex(src=terminals['H'], snk=terminals['T'], bw=next(iter(path)).bw)
            _create_track(tindex.src, tindex.snk, fabric, processed_tracks)

    def _connect_cb(cb):
        _bw = int(cb.get('bus').replace('BUS', ''), 0)
        _ps = (row, col)

        fa = int(cb.get('feature_address'), 0)
        sel_w = int(cb.find('sel_width').text, 0)

        for mux in cb.findall("mux"):
            _port = mux.get('snk')
            snkindex = _get_index(_ps, _port, _resource, bw=_bw, tile_row=row)

            for src in mux.findall("src"):
                sel = int(src.get('sel'), 0)
                src_name = src.text
                srcindex = _get_index(_ps, src_name, _resource, 'i', _bw, row)

                # handle ports off the edge
                if srcindex not in fabric:
                    srcindex = _infer_src(_ps, srcindex, ftdata, fabric, io16_positions)
                    assert srcindex in fabric, \
                      "Should be an existing IO, or a just added off-the-edge node"

                assert srcindex.bw == snkindex.bw, \
                    'Attempting to connect ports with different bus widths'

                tindex = _create_track(srcindex, snkindex, fabric, processed_tracks)
                config_engine[tindex] = config(feature_address=fa, sel_w=sel_w, sel=sel,
                                               src_name=src_name, snk_name=_port)

    def _connect_io(io_tile):
        # location to connect to should be embedded in it's index,
        # then just query fabric for that index to make a trackindex/track
        # inputs were already connected in _connect_sb

        # attach output tiles
        # these are INPUTs to the IO tile
        for out in io_tile.findall('input'):
            output_name = out.text
            _, out_bus, out_side, out_track = _match_io_name(output_name)
            output_index = _get_index((row, col), output_name, Resource.IO)
            rown, coln, _ = mapSide(row, col, out_side)
            src_ps = (rown, coln)

            dst_ps = (row, col)
            if out_bus == 1:
                # 1 bit IO bypass empty or IO16 tiles
                assert src_ps in ioempty_positions, "Expecting IO or empty tile"
                # shifts the positions
                temp = src_ps
                src_ps = _bypass(dst_ps, src_ps)
                dst_ps = temp
                del temp

            srcindex = muxindex(ps=src_ps, po=dst_ps,
                                resource=Resource.SB,
                                bw=out_bus, track=out_track,
                                port=None)

            assert srcindex in fabric, "Expecting valid port, got {}".format(srcindex)
            _create_track(srcindex, output_index, fabric, processed_tracks)

        # TODO: Figure out what to put in config engine

    elem2connector = {'sb': _connect_sb,
                      'cb': _connect_cb}

    for tile in root:
        # HACK -- currently doing nothing with global stalls
        if tile.get("type") in ignore_types:
            continue

        col = int(tile.get('col'), 0)
        row = int(tile.get('row'), 0)
        # note, memory tiles will add the sb row to y

        if tile.get("type"):
            _resource = resourcedict[tile.get("type")]
        else:
            _resource = Resource.PE

        for elem, connector in elem2connector.items():
            for tag in tile.findall(elem):
                connector(tag)

        if _resource == Resource.IO:
            _connect_io(tile)


# Helper Functions
def _get_index(ps, name, resource, direc='o', bw=None, tile_row=None):
    if resource == Resource.Mem:
        idx = _get_index_mem(ps, name, resource, direc, bw, tile_row)
    elif resource == Resource.IO:
        idx = _get_index_io(ps, name, resource, None, None, tile_row)
    else:
        idx = _get_index_regular(ps, name, resource, bw)
    return idx

def _get_index_regular(ps, name, resource, bw):
    row, col = ps

    p = re.compile('(?P<direc>in|out)'
                   '(?:_\d*)?_'
                    'BUS(?P<bus>\d+)_'
                    'S?(?P<side>\d+)_'
                    'T?(?P<track>\d+)')

    m = p.search(name)

    if not m:
        # This is a PE or Mem with a port
        return muxindex(resource=resource, ps=ps, bw=bw, port=name)
    else:
        # Switch Box
        signal_direc = m.group('direc')
        _side = Side(int(m.group('side'), 0))
        _track = int(m.group('track'), 0)
        _bus = int(m.group('bus'), 0)

        if bw is not None:
            assert _bus == bw, 'Expected bus width to be '
            '{} but it is {}'.format(bw, _bus)

        rown, coln, _ = mapSide(row, col, _side)

        if signal_direc == 'out':
            return muxindex(resource=Resource.SB, ps=ps, po=(rown, coln), bw=_bus, track=_track)
        elif signal_direc == 'in':
            # pself and pother swapped for in wires
            return muxindex(resource=Resource.SB, ps=(rown, coln), po=ps, bw=_bus, track=_track)
        else:
            raise RuntimeError("Parsed unhandled direction: {}".format(signal_direc))


def _get_index_io(ps, name, resource, direc, bw, tile_row):

    # io tiles have all the necessary information in the name and ps (position)
    assert direc is None, "direc unused for io tiles"
    assert bw is None, "Don't need bw for IO tile -- it's in name"
    assert tile_row is None, "tile_row is not needed"
    assert resource == Resource.IO, "Expecting an io tile"

    if bw == 1:
        direc_map = _PORT_TRANSLATION['BitIO']
    else:
        direc_map = _PORT_TRANSLATION['IO']

    row, col = ps
    _direc, _bus, _side, _track = _match_io_name(name)

    # retrieve neighbor location
    rown, coln, _ = mapSide(row, col, _side)

    return muxindex(resource=Resource.IO, ps=ps, po=None, bw=_bus, track=None, port=direc_map[_direc])

def _get_index_mem(ps, name, resource, direc, bw, tile_row):

    row, col = ps

    p = re.compile(r'(?P<mem_int>sb_wire_)?'
                   '(?P<direc>in|out)(?:_\d*)?_'
                   'BUS(?P<bus>\d+)_'
                   'S?(?P<side>\d+)_'
                   'T?(?P<track>\d+)')

    m = p.search(name)

    if not m:
        if direc == 'i':
            assert tile_row is not None
            return muxindex(resource=resource, ps=(tile_row, col), bw=bw, port=name)
        else:
            return muxindex(resource=resource, ps=ps, bw=bw, port=name)

    else:
        signal_direc = m.group('direc')
        _side = Side(int(m.group('side'), 0))
        _track = int(m.group('track'), 0)
        _bus = int(m.group('bus'), 0)

        if bw is not None:
            assert _bus == bw, 'Expected bus width to be '
            '{} but it is {}'.format(bw, _bus)

        if m.group('mem_int'):
            # internal memory wires have non-standard sides
            # need to do a mapping, overwriting _side
            b, _side, t = parse_mem_sb_wire(signal_direc, _side, _track, _bus, direc)
            # everything except for the side should stay the same
            assert b == _bus
            assert int(t) == _track

        rown, coln, _ = mapSide(row, col, _side)

        po = (rown, coln)

        if not m.group('mem_int') and signal_direc == 'in':
            # if incoming, switch direction
            po = ps
            ps = (rown, coln)
        elif m.group('mem_int') and direc == 'i':
            # switch for incoming
            # internal mem wires (sb_wire*) are used as sinks and sources and thus the signal_direc is meaningless
            # need to rely on the extra direc argument to determine if it's being used as a sink or source
            po = ps
            ps = (rown, coln)

        return muxindex(resource=Resource.SB, ps=ps, po=po, bw=_bus, track=_track)


def _bypass(ps, other_ps):
    '''
    Given a current position and a bypass tile (i.e. one that is skipped)
    position, returns the IO position, which is just one further in the
    same direction
    '''
    _side = pos_to_side(ps, other_ps)
    if _side == Side.N:
        io_ps = other_ps
        io_ps = (io_ps[0] - 1, io_ps[1])
    elif _side == Side.S:
        io_ps = other_ps
        io_ps = (io_ps[0] + 1, io_ps[1])
    elif _side == Side.E:
        io_ps = other_ps
        io_ps = (io_ps[0], io_ps[1] + 1)
    elif _side == Side.W:
        io_ps = other_ps
        io_ps = (io_ps[0], io_ps[1] - 1)
    else:
        raise RuntimeError("Unhandled side")

    return io_ps

def _infer_src(ps, srcindex, ftdata, fabric, io16_positions):

    # Special IO handling
    # 1 bit IOs skip a tile
    # 16 bit IOs don't
    if srcindex.ps in ioempty_positions:
        io_ps = srcindex.ps
        # 1 bit IO bypasses empty or IO16 Bit tiles
        if srcindex.bw == 1:
            io_ps = _bypass(ps, srcindex.ps)

        # construct IO's srcindex
        # uses some parameters from initial srcindex guess
        io_index = muxindex(ps=io_ps, po=None,
                            resource=Resource.IO,
                            bw=srcindex.bw,
                            track=None,
                            port="src")
        # If the IO exists
        # Counting on IOs being added correctly in proc_io
        if io_index in fabric:
            srcindex = io_index
        else:
            # create a new port
            fabric[srcindex] = port_wrapper(Port(srcindex, 'i'))

    elif srcindex not in ftdata.muxindices:
        # create a new port
        fabric[srcindex] = port_wrapper(Port(srcindex, 'i'))

    else:
        raise Warning("Feedthroughs in design. These have NOT been tested thoroughly.")

    return srcindex

def _match_io_name(name):
    p = re.compile(r'(?P<direc>in|out)_'
                   '(?P<bus>\d+)BIT_'
                   'S?(?P<side>\d+)_'
                   'T?(?P<track>\d+)')
    m = p.search(name)
    _direc = m.group('direc')
    _bus = int(m.group('bus'))
    _side = Side(int(m.group('side'), 0))
    _track = int(m.group('track'))

    return _direc, _bus, _side, _track

def _create_track(srcindex, snkindex, fabric, processed_tracks):
    assert snkindex.bw == srcindex.bw, "Bus Widths should match"
    tindex = trackindex(snk=snkindex, src=srcindex, bw=srcindex.bw)

    if tindex not in processed_tracks:
        processed_tracks.add(tindex)
        track = Track(fabric[srcindex].source,
                      fabric[snkindex].sink,
                      srcindex.bw)
        fabric[tindex] = track

    return tindex

def parse_board_info(f, fabric):
    '''
    Parses the board info file and adds to the fabric
    Needs to be called after parse_xml, and passed the constructed fabric
    '''

    board = json.load(f)
    fabric.board = BiMultiDict({int(k) : v for k, v in board.items() if k != 'C'})
