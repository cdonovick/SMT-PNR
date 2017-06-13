from collections import defaultdict
from functools import partial
import os
import re
import sys

import lxml.etree as ET

from design.module import Resource
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
                    if vnet.dst.resource == Resource.Reg:
                        p = re.compile(r'(?:sb_wire_)?(?:in|out)(?:_\d*)?_BUS\d*_S?(?P<side>\d+)_T?(?P<track>\d+)')
                        m = p.search(snk)
                        _side = m.group('side')
                        _track = m.group('track')

                        if (x,y,_track,_side) == p_state[vnet.dst]:
                            assert mux.get('configr') is not None
                            print("good shit")
                            configr = int(mux.get('configr'))
                            reg = configr // 32
                            offset = configr % 32
                            data[reg] |= 1 << offset
                            comment[reg][(offset, offset)] = 'latch wire {} ({}) before connecting to {}'.format(src.get('sel'), src.text, snk)

                    configl = int(mux.get('configl'))
                    reg = configl // 32
                    offset = configl % 32
                    data[reg] |= int(src.get('sel')) << offset
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
                    print(mod)
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
        for net in design.physical_nets:
            f.write('{} -> {}:\n'.format(net.src.name, net.dst.name))
            f.write(str(r_state[(net, 'debug')]))
            f.write("\n")
