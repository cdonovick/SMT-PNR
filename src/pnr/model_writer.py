import xml.etree.ElementTree as ET
import os


def write_to_xml(inpath, outpath):
    def model_write(p_state, r_state):
        with open(inpath, 'r') as f:
            tree = ET.parse(f)

        root = tree.getroot()

        for tile in root:
            x = int(tile.get('col'))
            y = int(tile.get('row'))
            tile_used = False
            for cb in tile.findall('cb'):
                cb_used = False
                for mux in cb.findall('mux'):
                    snk = mux.get('snk')
                    mux_used = False
                    for src in mux.findall('src'):
                        if (x, y, 'CB', snk, src.text) in r_state.I:
                            cb_used = True
                            mux_used = True
                            tile_used = True
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
                            tile_used = True
                        else:
                            mux.remove(src)
                    if not mux_used:
                        sb.remove(mux)

                for ft in sb.findall('ft'):
                    snk = ft.get('snk')
                    ft_used = False
                    for src in ft.findall('src'):
                        if (x, y, 'SB', snk, src.text) in r_state.I:
                            sb_used = True
                            ft_used = True
                            tile_used = True

                    if not ft_used:
                        sb.remove(ft)
                        
                if not sb_used:
                    tile.remove(sb)

            if (x, y) in p_state.I:
                op = tile.find('opcode')
                ET.SubElement(op, p_state.I[(x,y)][0].op)

            if not tile_used:
                root.remove(tile)

        with open(outpath, 'w') as f:
            tree.write(f, encoding='unicode')

    return model_write
        
                  
