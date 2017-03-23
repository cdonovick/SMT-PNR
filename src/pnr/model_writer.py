import lxml.etree as ET
import os
import re
from fabric.fabricfuns import parse_name, mapSide


def write_to_xml(inpath, outpath, io_outpath):
    def model_write(p_state, r_state):
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
                        if (x, y, 'CB', snk, src.text) in r_state.I:
                            cb_used = True
                            mux_used = True
                            ioroute[snk] = src.text
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
                        if (x, y, 'SB', snk, src.text) in r_state.I:
                            sb_used = True
                            mux_used = True
                            if src.text == 'pe_out_res':
                                ioroute['out'] = snk
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
                if op_name == 'io':
                    io = ET.SubElement(ioroot, 'io')
                    io.set('name', p_state.I[(x,y)][0].op_atr['name'])
                    iotype = p_state.I[(x,y)][0].op_atr['type']
                    io.set('type', iotype)
                    iotile = ET.SubElement(io, 'tile')
                    iotile.text = tile_addr
                    if 'a' not in ioroute and 'out' not in ioroute:
                        raise RuntimeError('An invariant is broken...')
                    if iotype == 'source':
                        _, _, _, track = parse_name(ioroute['out'])
                    else:
                        _, _, _, track = parse_name(ioroute['a'])

                    ioside = ET.SubElement(io, 'side')

                    #infer the side
                    if x == 0:
                        side = 'S2'
                    else:
                        side = 'S3'
                    
                    ioside.text = side
                    iotrack = ET.SubElement(io, 'track')
                    iotrack.text = str(track)
                        
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

    return model_write
                  
