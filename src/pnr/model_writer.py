import lxml.etree as ET
import os


def write_to_xml(inpath, outpath):
    def model_write(p_state, r_state):
        #with open(inpath, 'r') as f:
        #    tree = ET.parse(f)
        tree = ET.parse(inpath)

        root = tree.getroot()

        for tile in root:
            y = int(tile.get('row'))
            x = int(tile.get('col'))
            for cb in tile.findall('cb'):
                cb_used = False
                for mux in cb.findall('mux'):
                    snk = mux.get('snk')
                    mux_used = False
                    for src in mux.findall('src'):
                        if (x, y, 'CB', snk, src.text) in r_state.I:
                            cb_used = True
                            mux_used = True
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
                op = ET.SubElement(opcode, p_state.I[(x,y)][0].op)

        #with open(outpath, 'w') as f:
            #tree.write(f, encoding='unicode')
        tree.write(outpath)

    return model_write
                  
