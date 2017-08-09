from collections import defaultdict
from functools import partial
import sys
import itertools

from pnrdoctor.design.module import Resource
from pnrdoctor.fabric.fabricutils import muxindex, trackindex
from pnrdoctor.config import Annotations
from .pnrutils import configindex
from pnrdoctor.util import smart_open, Mask, IdentDict, STAR

__all__ = ['write_debug', 'write_route_debug', 'write_bitstream']

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

_mem_translate = {
    'mode' : {
        'linebuffer' : 0,
        'fifo'       : 1,
        'ram'        : 2, #sram in the CGRA
    },
    'fifo_depth' : IdentDict(),
    'almost_full_count' : IdentDict(),
    'chain_enable' : IdentDict(),
    'tile_en' : IdentDict(),
}


def write_bitstream(fabric, bitstream, config_engine, annotate, p_state, r_state):
    # -------------------------------------------------
    # write_bitsream utilities
    # -------------------------------------------------

    def _proc_cb(port):
        data = defaultdict(int)
        comment = defaultdict(dict)

        feature_address = None

        # see fabric.fabricutils for indexing scheme documentation
        snkindex = muxindex(resource=mod.resource, ps=(x, y), po=STAR, bw=layer,
                            track=STAR, port=port)

        for tindex in fabric.matching_keys(trackindex(snk=snkindex, src=STAR, bw=STAR)):
            if tindex in r_state.I:
                c = config_engine[tindex]
                feature_address = c.feature_address
                data[0] = c.sel
                comment[0][(c.sel_w-1, 0)] = Annotations.connect_wire(data[0], c.src_name,
                                                                    c.snk_name, row=y, col=x)

        return data, comment, feature_address


    def _proc_sb():
        data = defaultdict(lambda : Mask(size=_bit_widths['data'], MSB0=False))
        comment = defaultdict(dict)

        feature_address = None

        all_mux_indices = muxindex(resource=Resource.SB, ps=(x, y), po=STAR,
                                   bw=layer, track=STAR, port=None)

        for mindex in fabric.matching_keys(all_mux_indices):
            for tindex in fabric.matching_keys(trackindex(snk=mindex, src=STAR, bw=layer)):
                if tindex in r_state.I:
                    c = config_engine[tindex]
                    feature_address = c.feature_address
                    vnet = r_state.I[tindex][0]

                    # check if the dst is a register
                    # and if the current track is the last track in the path
                    # i.e. the one that should be registered
                    if vnet.dst.resource == Resource.Reg and tindex == r_state[vnet][-1]:
                        assert hasattr(c, 'configr')
                        assert c.configr is not None, 'Expecting a register at {} but has config={}'.format(tindex, c.__dict__)
                        reg = c.configr // 32
                        offset = c.configr % 32
                        data[reg] |= 1 << offset
                        comment[reg][(offset, offset)] = Annotations.latch_wire(c.snk_name, row=y, col=x)

                    reg = c.configl // 32
                    offset = c.configl % 32
                    data[reg] |= c.sel << offset
                    comment[reg][(c.sel_w + offset - 1, offset)] = Annotations.connect_wire(c.sel, c.src_name, c.snk_name, row=y, col=x)

        return data, comment, feature_address


    def _proc_pe(mod):
        data = defaultdict(lambda : Mask(size=_bit_widths['data'], MSB0=False))
        comment = defaultdict(dict)

        assert mod.resource == Resource.PE
        if mod.type_ == 'PE':
            data[_pe_reg['op']] |= _op_codes[mod.config]
            comment[_pe_reg['op']][(4,0)] = 'op = {}'.format(mod.config)

            for port in mod.inputs:
                if len(mod.inputs[port]) > 1:
                    #HACK if there are multiple drivers then grab the register
                    for net in mod.inputs[port]:
                        if net.src.type_ == 'Reg' and net.src.resource == Resource.Fused:
                            break
                else:
                    net = mod.inputs[port][0]

                src = net.src
                if src.type_ == 'Const':
                    data[_pe_reg[port]] |= src.config # load 'a' reg with const
                    comment[_pe_reg[port]][(15,0)] = Annotations.init_reg(port, src.config)
                    comment[_pe_reg['op']][2*(_read_wire[port],)] = Annotations.read_from('reg', port)
                elif src.type_ == 'Reg' and src.resource == Resource.Fused:
                    data[_pe_reg['op']][_load_reg[port]] |= 1 # load reg with wire
                    comment[_pe_reg['op']][2*(_load_reg[port],)] = Annotations.load_reg(port)
                    comment[_pe_reg['op']][2*(_read_wire[port],)] = Annotations.read_from('reg', port)
                else:
                    data[_pe_reg['op']][_read_wire[port]] |=  1 # read from wire
                    comment[_pe_reg['op']][2*(_read_wire[port],)]  = Annotations.read_from('wire', port)


        elif mod.type_ == 'IO':
            data[_pe_reg['op']] = _op_codes[mod.config]

            if mod.config == 'i':
                comment[_pe_reg['op']][(4, 0)] = Annotations.op_config('op', 'input')
                data[_pe_reg['a']]  = 0xffffffff
                data[_pe_reg['b']]  = 0xffffffff
            else:
                comment[_pe_reg['op']][(4, 0)] = Annotations.op_config('op', 'output')
                data[_pe_reg['b']]  = 0xffffffff


        return data, comment, config_engine[configindex(resource=Resource.PE, ps=(x, y))].feature_address

    def _proc_mem(mod):
        data = defaultdict(lambda : Mask(size=_bit_widths['data'], MSB0=False))
        comment = defaultdict(dict)

        assert mod.resource == Resource.Mem
        for opt, value in mod.config.items():

            val = int(_mem_translate[opt][value])

            ci = configindex(resource=Resource.Mem, ps=(x, y))
            c = config_engine[ci]

            bitl = c[opt].bitl
            sel_w = c[opt].bith - bitl + 1
            reg = bitl // 32
            offset = bitl % 32

            assert val.bit_length() <= sel_w
            data[reg] |= val << offset
            comment[reg][(sel_w + offset - 1, offset)] = Annotations.op_config(opt, value)

        return data, comment, c.feature_address

    def _write(data, tile_address, feature_address, bs, comment):
        for reg in data:
            if annotate:
                suffix =  Annotations.format_comment(comment[reg])
            else:
                suffix = ''
            bs.write(_format_line(tile_address, feature_address, reg, int(data[reg])) + suffix)

    def _format_line(tile, feature, reg, data):
        ts = _format_elem(tile, _bit_widths['tile'])
        fs = _format_elem(feature, _bit_widths['feature'])
        rs = _format_elem(reg, _bit_widths['reg'])
        ds = _format_elem(data, _bit_widths['data'])
        return rs+fs+ts+' '+ds+'\n'

    def _format_elem(elem, elem_bits):
        return '{:0{bits}X}'.format(elem, bits=elem_bits//4)


    # -------------------------------------------------
    # write_bitsream
    # -------------------------------------------------
    res2fun = {
            Resource.Mem : _proc_mem,
            Resource.PE  : _proc_pe
    }

    # open bit stream then loop
    with open(bitstream, 'w') as bs:

        # HACK: Hardcoded layer
        for layer in {16}:
            for x, y in itertools.product(range(fabric.cols), range(fabric.rows)):
                tile_addr = config_engine[(x, y)].tile_addr
                data, comment, feature_address = _proc_sb()
                _write(data, tile_addr, feature_address, bs, comment)
                if (x, y) in p_state.I:
                    for mod in p_state.I[(x, y)]:
                        if mod.resource != Resource.Reg:
                            for port in fabric.port_names[(mod.resource, layer)].sinks:
                                data, comment, feature_address = _proc_cb(port)
                                _write(data, tile_addr, feature_address, bs, comment)

                            data, comment, feature_address = res2fun[mod.resource](mod)
                            _write(data, tile_addr, feature_address, bs, comment)


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
