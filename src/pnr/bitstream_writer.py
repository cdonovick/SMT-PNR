import lxml.etree as ET
import os
import re
from fabric.fabricfuns import parse_name, mapSide
from fabric import Side
from functools import partial
from collections import defaultdict

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
    'source'    : 0xf0,
    'sink'      : 0xff,
}

_pe_reg = {
    'op' : 0xff,
    'a'  : 0xf0,
    'b'  : 0xf1,
}

def bitstream_writer(cgra_xml, bitstream, p_state, r_state):
    def _proc_cb(cb):
        data = defaultdict(int)
        for mux in cb.findall('mux'):
            snk = mux.get('snk')
            for src in mux.findall('src'):
                if (x, y, 'CB', snk, src.text) in r_state.I:
                    # reg == 0 for all cb
                    data[0] = int(src.get('sel'))
        return data

    def _proc_sb(sb):
        data = defaultdict(int)
        for mux in sb.findall('mux'):
            snk = mux.get('snk')
            for src in mux.findall('src'):
                if (x, y, 'SB', snk, src.text) in r_state.I:
                    # if latched
                    # set bit 1 << (sb.get('configr') % 32) at data[configr//32]
                    configl = int(mux.get('configl'))
                    reg = configl // 32
                    offset = configl % 32
                    data[reg] |= int(src.get('sel')) << offset
        return data


    def _proc_pe(pe):
        data = defaultdict(int)
        if (x, y) in p_state.I:
            op_name = p_state.I[(x,y)][0].op
            op_text = p_state.I[(x,y)][0].op_val
            if op_name == 'const':
                #set op to add
                data[_pe_reg['op']] = _op_codes['add']
                data[_pe_reg['a']]  = int(op_text)
                data[_pe_reg['b']]  = 0
            elif op_name == 'io':
                iotype = p_state.I[(x,y)][0].op_atr['type']
                data[_pe_reg['op']] = _op_codes[iotype]
                if iotype == 'source':
                    data[_pe_reg['a']]  = 0xffffffff
                    data[_pe_reg['b']]  = 0xffffffff
                else:
                    data[_pe_reg['b']]  = 0x0
            else:
                data[_pe_reg['op']] = _op_codes[op_name]
        return data

    def _write(data, ta, fa, bs):
        for r,d in data.items():
            bs.write(_format_line(ta, fa, r, d) + '\n')

    def _format_elem(elem, elem_bits):
        return '{:0{bits}X}'.format(elem, bits=elem_bits//4)

    def _format_line(tile, feature, reg, data):
        ts = _format_elem(tile, _bit_widths['tile'])
        fs = _format_elem(feature, _bit_widths['feature'])
        rs = _format_elem(reg, _bit_widths['reg'])
        ds = _format_elem(data, _bit_widths['data'])
        return rs+fs+ts+' '+ds


    tree = ET.parse(cgra_xml)
    root = tree.getroot()
    with open(bitstream, 'w') as bs: 
        for tile in root:
                tile_address = int(tile.get('tile_addr'))

                y = int(tile.get('row'))
                x = int(tile.get('col'))
                for cb in tile.findall('cb'):
                    feature_address = int(cb.get('feature_address'))
                    data = _proc_cb(cb)
                    _write(data, tile_address, feature_address, bs)


                for sb in tile.findall('sb'):
                    feature_address = int(sb.get('feature_address'))
                    data = _proc_sb(sb)
                    _write(data, tile_address, feature_address, bs)

                for pe in tile.findall('pe'):
                    feature_address = int(pe.get('feature_address'))
                    data = _proc_pe(pe)
                    _write(data, tile_address, feature_address, bs)
                    

