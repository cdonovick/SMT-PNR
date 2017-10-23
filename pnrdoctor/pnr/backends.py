from collections import defaultdict
from functools import partial
import sys
import itertools

from pnrdoctor.design.module import Resource, Layer
from pnrdoctor.fabric.fabricutils import muxindex, trackindex
from pnrdoctor.config import Annotations
from pnrdoctor.util import smart_open, Mask, IdentDict, STAR, SetList, BiMultiDict, SortedDict
from .pnrutils import configindex

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
    'alu_op'    : 5,
    'lut_value' : 2, #8,
}

_op_translate = {
    'alu_op' : {
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
    },
    'lut_value' : IdentDict(),
}

_pe_reg = {
    'alu_op'    : 0xff,
    'lut_value' : 0x00,
    'op_a_in'   : 0xf0,
    'op_b_in'   : 0xf1,
}


_port_offsets = {
    'op_d_p_in' : 8, #24,
    'op_c_in'   : 10, #20,
    'op_b_in'   : 12, #18,
    'op_a_in'   : 14, #16,
}

_reg_mode = {
    'CONST'  : 0x0,
    'VALID'  : 0x1,
    'BYPASS' : 0x2,
    'DELAY'  : 0x3,
}

_LUT_ENABLE = 7 #9

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


def write_bitstream(fabric, bitstream, config_engine, annotate, debug=False):
    # -------------------------------------------------
    # write_bitsream utilities
    # -------------------------------------------------

    p_state = config_engine.p_state
    r_state = config_engine.r_state

    def _proc_cb(port, tile_addr, b_dict, c_dict, d_dict):
        feature_address = None

        # see fabric.fabricutils for indexing scheme documentation
        snkindex = muxindex(resource=mod.resource, ps=(row, col), po=STAR, bw=layer,
                            track=STAR, port=port)

        tindexlist = [tindex for tindex in t_indices if tindex.snk == snkindex]

        assert len(tindexlist) <= 1, \
          'There should only be one driver of a PE input but have \n{}'.format(tindexlist)

        # will loop at most once
        for tindex in tindexlist:
            c = config_engine[tindex]
            feature_address = c.feature_address
            reg = 0 # true for all cbs
            idx = (tile_addr, feature_address, reg)
            b_dict[idx] |= c.sel
            c_dict[idx][(c.sel_w-1, 0)] = Annotations.connect_wire(c.sel, c.src_name, c.snk_name, row=row, col=col)

            vtie = r_state.I[tindex][0]
            d_dict[idx][(c.sel_w-1, 0)] = id_fmt.format(vtie.id)



    def _proc_sb(t_indices, tile_addr, b_dict, c_dict, d_dict):
        feature_address = None

        for tindex in t_indices:
            if tindex.snk.port:
                # this is a connection box, because it has a port
                # ignore it
                continue

            c = config_engine[tindex]
            feature_address = c.feature_address
            vtie = r_state.I[tindex][0]

            # check if the dst is a register
            # and if the current track is the last track in the path
            # i.e. the one that should be registered
            if vtie.dst.resource == Resource.Reg and tindex == r_state[vtie][-1]:
                assert hasattr(c, 'configr')
                assert c.configr is not None, 'Expecting a register at {} but has config={}'.format(tindex, c.__dict__)
                reg = c.configr // 32
                idx = (tile_addr, feature_address, reg)

                offset = c.configr % 32
                b_dict[idx] |= 1 << offset
                c_dict[idx][(offset, offset)] = Annotations.latch_wire(c.snk_name, row=row, col=col)
                d_dict[idx][(offset, offset)] = id_fmt.format(vtie.id)

            reg = c.configl // 32
            idx = (tile_addr, feature_address, reg)

            offset = c.configl % 32
            b_dict[idx] |= c.sel << offset
            c_dict[idx][(c.sel_w + offset - 1, offset)] = Annotations.connect_wire(c.sel, c.src_name, c.snk_name, row=row, col=col)
            d_dict[idx][(c.sel_w + offset - 1, offset)] = id_fmt.format(vtie.id)



    def _proc_pe(mod, tile_addr, b_dict, c_dict, d_dict):
        assert mod.resource == Resource.PE
        feature_address = config_engine[configindex(resource=Resource.PE, ps=(row, col))].feature_address

        if mod.type_ == 'PE':
            for k in mod.config:
                if k in _op_translate:
                    d = _op_translate[k]
                    reg = _pe_reg[k]
                    idx = (tile_addr, feature_address, reg)

                    if d[mod.config[k]].bit_length() > _bit_widths[k]:
                        raise ValueError("Config field `{}' is {} bits. Given value `{}' requires {} bits".format(
                            k,
                            _bit_widths[k],
                            d[mod.config[k]],
                            d[mod.config[k]].bit_length()
                            ))

                    b_dict[idx] |= d[mod.config[k]]
                    c_dict[idx][(_bit_widths[k]-1, 0)] = '{} = {}'.format(k, mod.config[k])
                    d_dict[idx][(_bit_widths[k]-1, 0)] = id_fmt.format(mod.id)


            if 'lut_value' in mod.config:
                reg = _pe_reg['alu_op']
                idx = (tile_addr, feature_address, reg)

                b_dict[idx][_LUT_ENABLE] |= 1
                c_dict[idx][(_LUT_ENABLE, _LUT_ENABLE)] = 'Enable Lut'
                d_dict[idx][(_LUT_ENABLE, _LUT_ENABLE)] = id_fmt.format(mod.id)


            for port in mod.inputs:
                tie = mod.inputs[port]

                src = tie.src
                if port not in _port_offsets:
                    assert src.type_ != 'Const'
                    assert port not in mod.registered_ports
                    continue

                if src.type_ == 'Const':
                    reg = _pe_reg[port]
                    idx = (tile_addr, feature_address, reg)


                    b_dict[idx] |= src.config # load 'op_a_in' reg with const
                    c_dict[idx][(15,0)] = Annotations.init_reg(port, src.config)
                    d_dict[idx][(15,0)] = id_fmt.format(mod.id)

                    reg  = _pe_reg['alu_op']
                    idx = (tile_addr, feature_address, reg)

                    offset =  _port_offsets[port]
                    b_dict[idx] |=  _reg_mode['CONST'] << offset
                    c_dict[idx][(offset+1, offset)] = '{}: REG_CONST'.format(port)
                    d_dict[idx][(offset+1, offset)] = id_fmt.format(mod.id)

                elif port in mod.registered_ports:
                    reg = _pe_reg['alu_op']
                    idx = (tile_addr, feature_address, reg)
                    offset =  _port_offsets[port]
                    b_dict[idx] |=  _reg_mode['DELAY'] << offset
                    c_dict[idx][(offset+1, offset)] = '{}: REG_DELAY'.format(port)
                    d_dict[idx][(offset+1, offset)] = id_fmt.format(mod.id)

                else:
                    reg = _pe_reg['alu_op']
                    idx = (tile_addr, feature_address, reg)
                    offset =  _port_offsets[port]

                    b_dict[idx] |=  _reg_mode['BYPASS'] << offset
                    c_dict[idx][(offset+1, offset)] = '{}: REG_BYPASS'.format(port)
                    d_dict[idx][(offset+1, offset)] = id_fmt.format(mod.id)



        elif mod.type_ == 'IO':
            reg = _pe_reg['alu_op']
            idx = (tile_addr, feature_address, reg)

            b_dict[idx] |= _op_translate['alu_op'][mod.config]


            if mod.config == 'i':
                c_dict[idx][(5, 0)] = Annotations.op_config('alu_op', 'input')
                d_dict[idx][(5, 0)] = id_fmt.format(mod.id)

                reg = _pe_reg['op_a_in']
                idx = (tile_addr, feature_address, reg)
                b_dict[idx]  = 0xffffffff

                reg = _pe_reg['op_b_in']
                idx = (tile_addr, feature_address, reg)
                b_dict[idx]  = 0xffffffff
            else:
                c_dict[idx][(5, 0)] = Annotations.op_config('alu_op', 'output')
                d_dict[idx][(5, 0)] = id_fmt.format(mod.id)

                reg = _pe_reg['op_b_in']
                idx = (tile_addr, feature_address, reg)
                b_dict[idx]  = 0xffffffff


        else:
            raise ValueError("Unkown mod.type_ : `{}'".format(mod.type_))

    def _proc_mem(mod, tile_addr, b_dict, c_dict, d_dict):
        assert mod.resource == Resource.Mem
        for opt, value in mod.config.items():

            val = int(_mem_translate[opt][value])

            ci = configindex(resource=Resource.Mem, ps=(row, col))
            c = config_engine[ci]

            bitl = c[opt].bitl
            sel_w = c[opt].bith - bitl + 1
            reg = bitl // 32
            offset = bitl % 32

            assert val.bit_length() <= sel_w
            idx = (tile_addr, c.feature_address, reg)

            b_dict[idx] |= val << offset
            c_dict[idx][(sel_w + offset - 1, offset)] = Annotations.op_config(opt, value)
            d_dict[idx][(sel_w + offset - 1, offset)] = id_fmt.format(mod.id)


    def _write(bs, idx, data, comments):
        tile_address, feature_address, reg = idx
        suffix =  Annotations.format_comment(comments) 

        bs.write(_format_line(tile_address, feature_address, reg, int(data)) + suffix)

    def _format_line(tile, feature, reg, data):
        ts = _format_elem(tile, _bit_widths['tile'])
        fs = _format_elem(feature, _bit_widths['feature'])
        rs = _format_elem(reg, _bit_widths['reg'])
        ds = _format_elem(data, _bit_widths['data'])
        return rs+fs+ts+' '+ds+'\n'

    def _format_elem(elem, elem_bits):
        return '{:0{bits}X}'.format(elem, bits=elem_bits//4)


    def _is_debug_tie(tie):
        return isinstance(tie, tuple) and len(tie) == 2 and tie[1] == 'debug'

    # -------------------------------------------------
    # write_bitsream
    # -------------------------------------------------
    res2fun = {
            Resource.Mem : _proc_mem,
            Resource.PE  : _proc_pe
    }

    # open bit stream then loop
    with open(bitstream, 'w') as bs:

        # Process r_state
        # organize track indices by location
        processed_r_state = defaultdict(SetList)
        for k, tindex in r_state.items():
            if _is_debug_tie(k):
                # this is debug information
                continue

            # index by position (.ps) and bus width (.bw)
            processed_r_state[(tindex.snk.ps, tindex.bw)].add(tindex)

        pos_map = BiMultiDict(default=True)
        id_fmt = ''
        if debug:
            id_len = max(
                    max(len(str(m.id)) for m in p_state),
                    max(len(str(t.id)) for t in r_state if not _is_debug_tie(t)),
                    )
            id_fmt = '{' + ':0{l}'.format(l=id_len) + '}'

            for mod in p_state:
                bs.write(('# ' + id_fmt + ' := {}\n').format(mod.id, mod.name))
            bs.write('\n')
            for tie in r_state:
                if _is_debug_tie(tie):
                    continue
                bs.write(('# ' + id_fmt + ' := {}\n').format(tie.id, tie))
            bs.write('\n')
            if annotate:
                id_fmt = ' ; ' + id_fmt
            else:
                id_fmt = ' # ' + id_fmt



        for module,reg in p_state.items():
            if module.resource != Resource.Reg:
                pos_map[module] = reg.position[fabric.rows_dim], reg.position[fabric.cols_dim]

        #(tile_addr, feature_addres, reg) -> data
        b_dict = defaultdict(lambda : Mask(size=_bit_widths['data'], MSB0=False))

        #(tile_addr, feature_addres, reg) -> (bith, bitl) -> comment
        c_dict = defaultdict(lambda : defaultdict(str))
        d_dict = defaultdict(lambda : defaultdict(str))
        # for each position and layer, process all the tracks and modules
        for pos, layer in sorted(processed_r_state):
            tile_addr = config_engine[pos].tile_addr
            row, col = pos
            t_indices = processed_r_state[(pos, layer)]

            _proc_sb(t_indices, tile_addr, b_dict, c_dict, d_dict)
            #_write(data, tile_addr, feature_address, bs, comment)
            for mod in pos_map.I[pos]:
                for port in fabric.port_names[(mod.resource, layer)].sinks:
                    _proc_cb(port, tile_addr, b_dict, c_dict, d_dict)
                    #_write(data, tile_addr, feature_address, bs, comment)

                res2fun[mod.resource](mod, tile_addr, b_dict, c_dict, d_dict)
                #_write(data, tile_addr, feature_address, bs, comment)

        assert b_dict.keys() >= c_dict.keys()
        assert c_dict.keys() == d_dict.keys(), c_dict

        #HACK `reset` unused dictionarys
        if not annotate:
            c_dict = defaultdict(lambda : defaultdict(str))
        if not debug:
            d_dict = defaultdict(lambda : defaultdict(str))

        #Merge comment and debug dict
        comments = defaultdict(lambda : defaultdict(str))
        for idx in b_dict:
            for bits in (c_dict[idx].keys() | d_dict[idx].keys()):
                comments[idx][bits] = c_dict[idx][bits] + d_dict[idx][bits]

        for idx in sorted(b_dict.keys()):
            _write(bs, idx, b_dict[idx], comments[idx])




def write_debug(design, output=sys.stdout):
    return partial(_write_debug, design, output)


def _write_debug(design, output, p_state, r_state):
    with smart_open(output) as f:
        for module in design.modules:
            try:
                pos = {d.name : v for d,v in p_state[module].position.items() if v is not None}
                pos.update({d.name : v for d,v in p_state[module].category.items() if v is not None} )
                if 'layer' in pos:
                    pos['layer'] = Layer(pos['layer']).name

                f.write("module: {} @ {})\n".format(module.name, pos))
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
        for tie in design.ties:
            f.write('{} -> {}:\n'.format(tie.src.name, tie.dst.name))
            f.write(str(r_state[(tie, 'debug')]))
            f.write("\n")
