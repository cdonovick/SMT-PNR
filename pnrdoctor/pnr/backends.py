from collections import defaultdict
from functools import partial
import sys
import itertools
import json

from pnrdoctor.design.module import Resource, Layer
from pnrdoctor.fabric.fabricutils import muxindex, trackindex
from pnrdoctor.config import Annotations
from pnrdoctor.util import smart_open, Mask, IdentDict, STAR, SetList, BiMultiDict, SortedDict
from .pnrutils import configindex

__all__ = ['write_debug', 'write_route_debug', 'write_bitstream', 'write_io_collateral']

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
    'lut_value' : 8,
}

_ONE_BIT_PORT = "res_p"
_LUT_REG = 0x00

_op_translate = {
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
    'lshr'      : 0x0f,
    'ashr'      : 0x10,
    'ashl'      : 0x11,
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

_const_reg = {
    'data0'   : (0xf0, 16,),
    'data1'   : (0xf1, 16,),
    'data2'   : (0xf2, 16,),
    'bit0'    : (0xf3,  1,),
    'bit1'    : (0xf4,  1,),
    'bit2'    : (0xf5,  1,),
}

#[(reg, (bith, bitll), value)]
#_op_reg = {
#    'alu_op'    : [(0xff, (5,0), None),]
#    'lut_value' : [(0x00, (8,0), None), (0xff, (9,9), 1),]
#}



_port_offsets = {
    'data0'   : 16,
    'data1'   : 18,
    'data2'   : 20,
    'bit0'    : 24,
    'bit1'    : 26,
    'bit2'    : 28,
}

_reg_mode = {
    'CONST'  : 0x0,
    'VALID'  : 0x1,
    'BYPASS' : 0x2,
    'DELAY'  : 0x3,
}


_mem_translate = {
    'mode' : {
        'linebuffer' : 0,
        'fifo'       : 1,
        'ram'        : 2, #sram in the CGRA
    },
    'depth' : IdentDict(),
    'almost_count' : IdentDict(),
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
                snkindex = tindex.snk
                assert snkindex in config_engine._config, "Expecting {} to be in config_engine".format(snkindex)
                reg_config = config_engine[snkindex]

                assert reg_config.bith == reg_config.bitl, "Expecting to only need to set one bit."
                idx = (tile_addr, feature_address, reg_config.reg_address)

                offset = reg_config.bith
                b_dict[idx] |= 1 << offset
                c_dict[idx][(offset, offset)] = Annotations.latch_wire(c.snk_name, row=row, col=col)
                d_dict[idx][(offset, offset)] = id_fmt.format(vtie.id)
            # set the default if needed
            else:
                snkindex = tindex.snk
                assert snkindex in config_engine._config, "Expecting {} to be in config_engine".format(snkindex)
                reg_config = config_engine[snkindex]
                assert reg_config.bith == reg_config.bitl, "Expecting to only need to set one bit."
                if reg_config.default != 0:
                    assert reg_config.default == 1, "Default should be 0 or 1 got {}".format(reg_config.default)
                    idx = (tile_addr, feature_address, reg_config.reg_address)
                    offset = reg_config.bith
                    b_dict[idx] &= ~(1 << offset)
                    c_dict[idx][(offset, offset)] = "Disabling register"
                    d_dict[idx][(offset, offset)] = id_fmt.format(vtie.id)

            bitl = c.bitl // 32
            bith = c.bith // 32

            assert bith//32 == bitl//32, 'Cross boundary register detected in SB'

            reg = c.bitl // 32
            idx = (tile_addr, feature_address, reg)

            offset = c.bitl % 32
            b_dict[idx] |= c.sel << offset
            c_dict[idx][(c.sel_w + offset - 1, offset)] = Annotations.connect_wire(c.sel, c.src_name, c.snk_name, row=row, col=col)
            d_dict[idx][(c.sel_w + offset - 1, offset)] = id_fmt.format(vtie.id)



    def _proc_pe(mod, tile_addr, b_dict, c_dict, d_dict):
        assert mod.resource == Resource.PE
        config = config_engine[configindex(resource=Resource.PE, ps=(row, col))]
        feature_address = config.feature_address
        flag_sel_config = config.opcode.flag_sel
        alu_op_config   = config.opcode.op
        signed_config   = config.opcode.signed

        if mod.type_ != 'PE':
            raise ValueError("Unkown mod.type_ : `{}'".format(mod.type_))

        for k in mod.config:
            bith = None
            bitl = None
            if k == 'alu_op':
                bith    = alu_op_config.bith
                bitl    = alu_op_config.bitl
                reg     = alu_op_config.reg_address + bitl//32
                offset  = bitl % 32
                val     = mod.config[k]
            elif k == 'signed':
                bith    = signed_config.bith
                bitl    = signed_config.bitl
                reg     = signed_config.reg_address + bitl//32
                offset  = bitl % 32
                val     = mod.config[k] 
            elif k == 'alu_op_debug':
                continue
            elif k == 'lut_value':
                reg = _LUT_REG
                offset = 0
                val = mod.config[k]
            elif k == 'flag_sel':
                bith    = flag_sel_config.bith
                bitl    = flag_sel_config.bitl
                reg     = flag_sel_config.reg_address + bitl//32
                offset  = bitl % 32
                val     = mod.config[k] 
            elif k == 'flag_sel_debug':
                continue
            else: 
                print(f'Unkown PE config option {k}')

            if bith is not None:
                assert bith//32 == bitl//32, 'Cross boundary register detected in PE'
                if val.bit_length() > bith-bitl+1:
                    raise ValueError("Config field `{}' is {} bits. Given value `{}' requires {} bits".format(
                        k,
                        bith-bitl+1,
                        val,
                        val.bit_length()
                        ))

            idx = (tile_addr, feature_address, reg)
            b_dict[idx] |= val << offset
            if bith is not None:
                c_dict[idx][(bith, bitl)] = '{} = {}'.format(k, mod.config[k])
                d_dict[idx][(bith, bitl)] = id_fmt.format(mod.id)
            else:
                c_dict[idx][(val.bit_length(), 0)] = '{} = {}'.format(k, mod.config[k])
                d_dict[idx][(val.bit_length(), 0)] = id_fmt.format(mod.id)


        for port in mod.inputs:
            tie = mod.inputs[port]
            src = tie.src

            if port not in _port_offsets:
                assert src.type_ != 'Const'
                assert port not in mod.registered_ports
                print(f'Unkown PE port {port}')
                continue

            if src.type_ == 'Const':
                reg, width = _const_reg[port]
                idx = (tile_addr, feature_address, reg)
                d = src.config
                if d.bit_length() > width:
                    raise ValueError("Const on port `{}' should be {} bits. Given value `{}' requires {} bits".format(
                        port,
                        width,
                        d,
                        d.bit_length()
                        ))

                b_dict[idx] |= d # load 'data0' reg with const
                c_dict[idx][(width-1,0)] = Annotations.init_reg(port, src.config)
                d_dict[idx][(width-1,0)] = id_fmt.format(mod.id)
                mode = 'CONST'

            elif port in mod.registered_ports:
                mode = 'DELAY'

            else:
                mode = 'BYPASS'

            idx = (tile_addr, feature_address, alu_op_config.reg_address + alu_op_config.bitl//32)
            offset =  _port_offsets[port]

            b_dict[idx] |=  _reg_mode[mode] << offset
            c_dict[idx][(offset+1, offset)] = '{}: REG_{}'.format(port, mode)
            d_dict[idx][(offset+1, offset)] = id_fmt.format(mod.id)


    def _proc_io(mod, tile_addr, b_dict, c_dict, d_dict):
        assert mod.resource == Resource.IO
        assert mod.layer != Layer.Combined

        io_groups_dim = fabric.io_groups_dim
        group = p_state[mod].category[io_groups_dim]

        assert (row,col) in fabric.io_groups[group, mod.layer]

        layer = mod.layer
        if layer == Layer.Bit:
            rcs = [(row, col)]
        else:
            rcs = list(fabric.io_groups[group, Layer.Bit])

        for rx,cx in rcs:
            c = config_engine[configindex(resource=Resource.IO, ps=(rx,cx))]
            t = config_engine[rx, cx].tile_addr

            #handle tri
            assert c.io_group == group
            val = c.tri.direction[mod.config]
            bitl = c.tri.bitl
            bith = c.tri.bith

            assert bith//32 == bitl//32, 'Cross boundary register detected in IO'
            sel_w = bith - bitl + 1
            reg =  c.tri.reg_address + bitl//32
            offset = bitl % 32

            assert val.bit_length() <= sel_w
            idx = (t, c.tri.feature_address, reg)
            b_dict[idx] |= val << offset
            c_dict[idx][(sel_w + offset - 1, offset)] = f'@ tile ({rx}, {cx}) IO Mode = {mod.config}'
            d_dict[idx][(sel_w + offset - 1, offset)] = id_fmt.format(mod.id)


            val = c.mux.sel[layer]
            bitl = c.mux.bitl
            bith = c.mux.bith
            assert bith//32 == bitl//32, 'Cross boundary register detected in IO'
            sel_w = bith - bitl + 1
            reg =  c.mux.reg_address + bitl//32
            offset = bitl % 32
            assert val.bit_length() <= sel_w

            idx = (t, c.mux.feature_address, reg)
            b_dict[idx] |= val << offset
            c_dict[idx][(sel_w + offset - 1, offset)] = f'@ tile ({rx}, {cx}) IO Width = {mod.layer.width}'
            d_dict[idx][(sel_w + offset - 1, offset)] = id_fmt.format(mod.id)


            #handle mux
            if layer == Layer.Bit:
                assert True
                #set mux src to 1
            else:
                assert layer == Layer.Data
                #set mux src to 16



    def _proc_mem(mod, tile_addr, b_dict, c_dict, d_dict):
        assert mod.resource == Resource.Mem
        for opt, value in mod.config.items():

            val = int(_mem_translate[opt][value])

            ci = configindex(resource=Resource.Mem, ps=(row, col))
            c = config_engine[ci]

            bitl = c[opt].bitl
            bith = c[opt].bith
            assert bith//32 == bitl//32, 'Cross boundary register detected in MEM'
            sel_w = bith - bitl + 1
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
            Resource.PE  : _proc_pe,
            Resource.IO  : _proc_io,
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

        for module,region in p_state.items():
            if module.resource != Resource.Reg:
                pos_map[module] = region.position[fabric.rows_dim], region.position[fabric.cols_dim]

        #HACK HACK HACK
        #(tile_addr, feature_addres, reg) -> data
        b_dict = defaultdict(lambda : Mask(size=_bit_widths['data'], MSB0=False))

        #(tile_addr, feature_addres, reg) -> (bith, bitl) -> comment
        c_dict = defaultdict(lambda : defaultdict(str))

        # Set default configuration for memory switchboxes
        for pos in fabric.locations[(Resource.Mem, Layer.Combined)]:
            tile_addr = config_engine[pos].tile_addr
            offset = 60
            b_dict[(tile_addr, 0, 1)] |= 1 << offset
            c_dict[(tile_addr, 0, 1)][(offset, offset)] = 'Set memory out_0_S0_T0 to passthrough by default'

        for idx in sorted(b_dict.keys()):
            _write(bs, idx, b_dict[idx], c_dict[idx])

        # Now start again
        #(tile_addr, feature_addres, reg) -> data
        b_dict = defaultdict(lambda : Mask(size=_bit_widths['data'], MSB0=False))

        #(tile_addr, feature_addres, reg) -> (bith, bitl) -> comment
        c_dict = defaultdict(lambda : defaultdict(str))
        d_dict = defaultdict(lambda : defaultdict(str))

        # Delay configuring all tiles except IO
        mods = []
        for mod,pos in pos_map.items():
            if mod.resource != Resource.IO:
                #HACK HACK HACK
                mods.append((mod,pos))
            else:
                tile_addr = config_engine[pos].tile_addr
                row, col = pos
                res2fun[mod.resource](mod, tile_addr, b_dict, c_dict, d_dict)

        # for each position and layer, process all the tracks and registers
        for pos, layer in sorted(processed_r_state):
            tile_addr = config_engine[pos].tile_addr
            row, col = pos
            t_indices = processed_r_state[(pos, layer)]
            _proc_sb(t_indices, tile_addr, b_dict, c_dict, d_dict)

            for mod in pos_map.I[pos]:
                if mod.resource != Resource.IO:
                    for port in fabric.port_names[(mod.resource, layer)].sinks:
                        _proc_cb(port, tile_addr, b_dict, c_dict, d_dict)

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

        #HACK HACK HACK do everything again for configuration
        #(tile_addr, feature_addres, reg) -> data
        b_dict = defaultdict(lambda : Mask(size=_bit_widths['data'], MSB0=False))

        #(tile_addr, feature_addres, reg) -> (bith, bitl) -> comment
        c_dict = defaultdict(lambda : defaultdict(str))
        d_dict = defaultdict(lambda : defaultdict(str))
        for mod,pos in mods:
            tile_addr = config_engine[pos].tile_addr
            row, col = pos
            res2fun[mod.resource](mod, tile_addr, b_dict, c_dict, d_dict)

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


def write_io_collateral(collateral_file, fabric, config_engine):
    p_state = config_engine.p_state
    rows_dim, cols_dim, io_groups_dim =  fabric.rows_dim, fabric.cols_dim, fabric.io_groups_dim,

    io_dict = dict()

    for module,region in p_state.items():
        if module.resource == Resource.IO:
            m_state = p_state[module]
            group = m_state.category[io_groups_dim]
            row, col = m_state.position[rows_dim], m_state.position[cols_dim]

            if module.layer == Layer.Bit:
                rcs = [(row, col)]
            else:
                rcs = list(fabric.io_groups[group, Layer.Bit])

            io_dict[module.name] = {
                    'width' : module.layer.width,
                    'mode'  : module.config,
                    'bits'  : dict()
            }

            for rx,cx in rcs:
                c = config_engine[configindex(resource=Resource.IO, ps=(rx,cx))]
                t = config_engine[rx, cx].tile_addr

                io_dict[module.name]['bits'][c.io_bit] = c.name

    with open(collateral_file, 'w') as f:
        json.dump(io_dict, f, sort_keys=True, indent=4)



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
