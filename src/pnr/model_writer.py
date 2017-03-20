import xml.etree.ElementTree as ET
import os


def write_to_xml(filepath):
    def model_write(fabric, design, p_state, r_state, vars, solver):
        tree = ET.parse(filepath)
        root = tree.getroot()

        for tile in root:
            x = int(tile.get('col'))
            y = int(tile.get('row'))
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
                            src.remove()
                    if not mux_used:
                        mux.remove()
                if not cb_used:
                    cb.remove()

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
                            src.remove()
                    if not mux_used:
                        mux.remove()
                if not sb_used:
                    sb.remove()

            if (x, y) in p_state.I:
                op = tile.find('opcode')

                #retrieve the opcde from somewhere
                #if opcode is a constant:
                    #const = ET.SubElement(op, 'constant')
                    #const.text = p_state.I[(x,y)].opcode
                #else:
                    #op.text = p_state.I[(x,y)].opcode
        filepath_noext = os.path.splitext(filepath)[0]

        tree.write(filepath_noext + '_pnr-ed.xml')

    return model_write
        
                  
