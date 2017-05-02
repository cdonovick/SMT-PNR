import lxml.etree as ET
import os
import re
from fabric.fabricfuns import parse_name, mapSide
from fabric import Side


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

    return model_write
                  
