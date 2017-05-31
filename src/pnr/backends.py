from collections import defaultdict
from functools import partial
import os
import re
import sys

import lxml.etree as ET

from fabric.fabricfuns import parse_name, mapSide
from fabric import Side
from util import smart_open, Mask

__all__ = ['write_debug', 'write_route_debug', 'write_bitstream', 'write_xml']

# -------------------------------------------------
# write_bitsream consants
# -------------------------------------------------
_bit_widths = {
    'address'   : 32,
    'data'      : 32,
    'tile'      : 16,
    'feature'   : 8,
    'reg'       : 8,
}

_op_codes = {
    'add'       : 0x00,
    'sub'       : 0x01,
    #2-3
    'lt'        : 0x04,
    'ge'        : 0x05,
    'xnorr'     : 0x06,
    'xorr'      : 0x07,
    'select'    : 0x08,
    #9-A
    'mull'      : 0x0b,
    'mulm'      : 0x0c,
    'mulh'      : 0x0d,
    #E
    'lrsh'      : 0x0f,
    'arsh'      : 0x10,
    'alsh'      : 0x11,
    'or'        : 0x12,
    'and'       : 0x13,
    'xor'       : 0x14,
    'not'       : 0x15,
    #mult->mull
    'mult'      : 0x0b,
    #mul->mull
    'mul'       : 0x0b,
    'i'         : 0xf0,
    'o'         : 0xff,
}

_pe_reg = {
    'op'  : 0xff,
    'a'   : 0xf0,
    'b'   : 0xf1,
}

_load_reg = {
    'a'   : 14,
    'b'   : 12,
    'c'   : 10,
    'd'   : 8,
}

_read_wire = {
    'a'   : 15,
    'b'   : 13,
    'c'   : 11,
    'd'   : 9,
}


def write_bitstream(cgra_xml, bitstream, annotate):
    return partial(_write_bitstream, cgra_xml, bitstream, annotate)


def _write_bitstream(cgra_xml, bitstream, annotate, p_state, r_state):
    # -------------------------------------------------
    # write_bitsream utilities
    # -------------------------------------------------
    def _proc_cb(cb):
        data = defaultdict(int)
        comment = defaultdict(dict)
        for tag in cb.findall('sel_width'):
            sel_w = int(tag.text)



        for mux in cb.findall('mux'):
            snk = mux.get('snk')
            for src in mux.findall('src'):
                if (x, y, 'CB', snk, src.text) in r_state.I:
                    # reg == 0 for all cb
                    data[0] = int(src.get('sel'))
                    comment[0][(sel_w-1, 0)] = 'connect wire {} ({}) to {}'.format(data[0], src.text, snk)

        return data, comment

    def _proc_sb(sb):
        data = defaultdict(lambda : Mask(size=_bit_widths['data'], MSB0=False))
        comment = defaultdict(dict)
        for tag in sb.findall('sel_width'):
            sel_w = int(tag.text)

        for mux in sb.findall('mux'):
            snk = mux.get('snk')
            for src in mux.findall('src'):
                r = (x, y, 'SB', snk, src.text)
                if r in r_state.I:
                    vnet = r_state.I[r][0]
                    if vnet.dst.resource == 'Reg' and mux.get('configr'):
                        configr = int(mux.get('configr'))
                        reg = configr // 32
                        offset = configr % 32
                        data[reg][offset:offset+1] = 1
                        comment[reg][(offset, offset)] = 'latch wire {} ({}) before connecting to {}'.format(src.get('sel'), src.text, snk)

                    configl = int(mux.get('configl'))
                    reg = configl // 32
                    offset = configl % 32
                    data[reg][offset: offset + sel_w] = int(src.get('sel'))
                    comment[reg][(sel_w + offset - 1, offset)] = 'connect wire {} ({}) to {}'.format(src.get('sel'), src.text, snk)

        return data,comment


    def _proc_pe(pe):
        data = defaultdict(lambda : Mask(size=_bit_widths['data'], MSB0=False))
        mask = defaultdict(lambda : Mask(size=_bit_widths['data'], MSB0=False))
        comment = defaultdict(dict)

        if (x, y) in p_state.I:
            mod = p_state.I[(x,y)][0]
            if mod.type_ == 'PE':
                data[_pe_reg['op']] |= _op_codes[mod.config]
                comment[_pe_reg['op']][(4,0)] = 'op = {}'.format(mod.config)

                for port in ('a', 'b'):
                    src = mod.inputs[port].src

                    if src.type_ == 'Const':
                        data[_pe_reg[port]] |= src.config # load 'a' reg with const
                        comment[_pe_reg[port]][(15,0)] = 'load `{}` reg with const: {}'.format(port, src.config)
                        comment[_pe_reg['op']][_read_wire[port]] = 'read from reg `{}`'.format(port)
                    elif src.type_ == 'Reg':
                        data[_pe_reg['op']][_load_reg[port]] |= 1 # load reg with wire
                        comment[_pe_reg['op']][_load_reg[port]] = 'load `{}` reg with wire'.format(port)
                        comment[_pe_reg['op']][_read_wire[port]] = 'read from reg `{}`'.format(port)
                    else:
                        data[_pe_reg['op']][_read_wire[port]] |=  1 # read from wire
                        comment[_pe_reg['op']][_read_wire[port]]  = 'read from wire `{}`'.format(port)

            elif mod.type_ == 'IO':
                data[_pe_reg['op']] = _op_codes[mod.config]

                if mod.config == 'i':
                    comment[_pe_reg['op']][(4, 0)] = 'op = input'
                    data[_pe_reg['a']]  = 0xffffffff
                    data[_pe_reg['b']]  = 0xffffffff
                else:
                    comment[_pe_reg['op']][(4, 0)] = 'op = output'
                    data[_pe_reg['b']]  = 0xffffffff


        return data, comment

    def _write(data, tile_address, feature_address, bs, comment):
        for reg in data:
            if annotate:
                suffix =  _format_comment(comment[reg])
            else:
                suffix = ''
            bs.write(_format_line(tile_address, feature_address, reg, int(data[reg])) + suffix)


    def _format_line(tile, feature, reg, data):
        ts = _format_elem(tile, _bit_widths['tile'])
        fs = _format_elem(feature, _bit_widths['feature'])
        rs = _format_elem(reg, _bit_widths['reg'])
        ds = _format_elem(data, _bit_widths['data'])
        return rs+fs+ts+' '+ds+'\n'

    def _format_comment(comment):
        s = []
        for bit, c in comment.items():
            s.append('# data[{}] : {}\n'.format(bit, c))

        return ''.join(s)


    def _format_elem(elem, elem_bits):
        return '{:0{bits}X}'.format(elem, bits=elem_bits//4)


    # -------------------------------------------------
    # write_bitsream
    # -------------------------------------------------
    tree = ET.parse(cgra_xml)
    root = tree.getroot()
    with open(bitstream, 'w') as bs:
        for tile in root:
                tile_address = int(tile.get('tile_addr'))

                y = int(tile.get('row'))
                x = int(tile.get('col'))
                for cb in tile.findall('cb'):
                    feature_address = int(cb.get('feature_address'))
                    data,comment = _proc_cb(cb)
                    _write(data, tile_address, feature_address, bs, comment)

                for sb in tile.findall('sb'):
                    feature_address = int(sb.get('feature_address'))
                    data,comment = _proc_sb(sb)
                    _write(data, tile_address, feature_address, bs, comment)

                for pe in tile.findall('pe'):
                    feature_address = int(pe.get('feature_address'))
                    data,comment = _proc_pe(pe)
                    _write(data, tile_address, feature_address, bs, comment)



def write_debug(design, output=sys.stdout):
    return partial(_write_debug, design, output)

def _write_debug(design, output, p_state, r_state):
    with smart_open(output) as f:
        for module in design.modules:
            try:
                f.write("module: {} @ {})\n".format(module.name, p_state[module][0]))
            except (KeyError, IndexError):
                f.write("module: {} is not placed\n".format(module.name))

            f.write("inputs: {}\n".format(', '.join(d.src.name for d in module.inputs.values())))
            f.write("outputs: {}\n".format(', '.join(d.dst.name for d in module.outputs.values())))
            f.write("\n")

#        for net in design.nets:
#            f.write("{} -> {}\n".format(net.src.name, net.dst.name))
#        f.write("\n")

def write_route_debug(design, output=sys.stdout):
    return partial(_write_route_debug, design, output)

def _write_route_debug(design, output, p_state, r_state):
    '''
       Debug printer four routing
       Nodes are currently named with the wire names from input file
       which is unfortunately verbose...
    '''
    with smart_open(output) as f:
        for net in design.virtual_nets:
            f.write('{} -> {}:\n'.format(net.src.name, net.dst.name))
            f.write(str(r_state[(net, 'debug')]))
            f.write("\n")


def write_xml(inpath, outpath, io_outpath):
    return partial(_write_xml, inpath, outpath, io_outpath)

def _write_xml(inpath, outpath, io_outpath, p_state, r_state):
    #with open(inpath, 'r') as f:
    #    tree = ET.parse(f)
    tree = ET.parse(inpath)

    root = tree.getroot()

    #root for io file
    ioroot = ET.Element('ioroot')

    for tile in root:
        tile_addr = tile.get('tile_addr')
        y = int(tile.get('row'))
        x = int(tile.get('col'))
        ioroute = dict()
        for cb in tile.findall('cb'):
            cb_used = False
            for mux in cb.findall('mux'):
                snk = mux.get('snk')
                mux_used = False
                for src in mux.findall('src'):
                    # construct a  to compare to r_state.I tracks
                    if (x, y, 'CB', snk, src.text) in r_state.I:
                        cb_used = True
                        mux_used = True
                        direc, bus, side, iotrack = parse_name(src.text)
                        #newx, ioy, newside = mapSide(x, y, side)
                        #newside = Side((side.value + 2) % 4)

                        if side.value == 0:
                            ioside = Side(2)
                            iox = x + 1
                            ioy = y
                        elif side.value == 1:
                            ioside = Side(3)
                            iox = x
                            ioy = y + 1
                        elif side.value == 2:
                            ioside = Side(0)
                            iox = x - 1
                            ioy = y
                        else:
                            ioside = Side(1)
                            iox = x
                            ioy = y - 1
                        ioroute[snk] = 'wire_' + str(ioy) + '_' + str(iox) + '_' + bus + '_S' + str(ioside.value) + '_T' + str(iotrack)
                    else:
                        mux.remove(src)
                if not mux_used:
                    cb.remove(mux)
            if not cb_used:
                tile.remove(cb)

        for sb in tile.findall('sb'):
            sb_used = False
            for mux in sb.findall('mux'):
                snk = mux.get('snk')
                mux_used = False
                for src in mux.findall('src'):
                    # create a  to compare to routed tracks in r_state.I
                    if (x, y, 'SB', snk, src.text) in r_state.I:
                        sb_used = True
                        mux_used = True
                        if src.text == 'pe_out_res':
                            direc, bus, side, iotrack = parse_name(snk)
                            ioside = side
                            iox = x
                            ioy = y
                            ioroute['out'] = 'wire_' + str(y) + '_' + str(x) + '_' + bus + '_S' + str(side.value) + '_T' + str(iotrack)
                    else:
                        mux.remove(src)
                if not mux_used:
                    sb.remove(mux)

            for ft in sb.findall('ft'):
                snk = ft.get('snk')
                src = ft.find('src')
                if (x, y, 'SB', snk, src.text) in r_state.I:
                    sb_used = True
                else:
                    sb.remove(ft)

            if not sb_used:
                tile.remove(sb)

        if (x, y) in p_state.I:
            opcode = tile.find('opcode')
            op_name = p_state.I[(x,y)][0].op
            op_text = p_state.I[(x,y)][0].op_val
            op = ET.SubElement(opcode, op_name)
            #print(op_name, y, x)
            if op_name == 'io' and ('a' in ioroute or 'out' in ioroute):
                io = ET.SubElement(ioroot, 'io')
                io.set('name', p_state.I[(x,y)][0].op_atr['name'])
                iotype = p_state.I[(x,y)][0].op_atr['type']
                #print(iotype, end=' ')
                io.set('type', iotype)
                iotile = ET.SubElement(io, 'tile')
                iotile.text = tile_addr
                if 'a' not in ioroute and 'out' not in ioroute:
                    raise RuntimeError('An invariant is broken...')


                iowname = ET.SubElement(io, 'wire_name')

                if iotype == 'source':
                    #print(ioroute['out'])
                    #_, _, side, track = parse_name(ioroute['out'])
                    iowname.text = ioroute['out']
                else:
                    #print(ioroute['a'])
                    #_, _, side, track = parse_name(ioroute['a'])
                    iowname.text = ioroute['a']


                ioside_element = ET.SubElement(io, 'side')

                #infer the side
                #if x == 0:
                #    edge_side = 'S2'
                #else:
                #    edge_side = 'S3'

                ioside_element.text = str(ioside.value)
                iotrack_element = ET.SubElement(io, 'track')
                iotrack_element.text = str(iotrack)
                iorow = ET.SubElement(io, 'row')
                iocol = ET.SubElement(io, 'col')
                iorow.text = str(ioy)
                iocol.text = str(iox)

            op.text = op_text

    processed_xml = re.sub(r'"', r"'", ET.tostring(root, pretty_print=True).decode('utf-8'))
    #processed_root = ET.fromstring(processed_xml)
    #processed_root.write(outpath)

    with open(outpath, 'w') as f:
        f.write(processed_xml)
        #tree.write(f, encoding='unicode')
    #tree.write(outpath)

    ioprocessed_xml = re.sub(r'"', r"'", ET.tostring(ioroot, pretty_print=True).decode('utf-8'))
    with open(io_outpath, 'w') as f:
        f.write(ioprocessed_xml)

