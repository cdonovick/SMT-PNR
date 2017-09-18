#!/usr/bin/env python3
import xml.etree.ElementTree as ET
import re
import copy

def hack(ifile, ofile, hack_port='c', hack_feature_adress='9'):
    tree = ET.parse(ifile)
    root = tree.getroot()

    d = dict()

    for tile in root:
        if 'pe' in tile.get('type').lower():
            onebit_cb = [elem for elem in tile.findall('cb') if elem.get('bus') == 'BUS1']
            assert len(onebit_cb) == 1, "Can't hack this fabric"

            d[tile] = onebit_cb[0]

    for tile,cb in d.items():
        assert cb.get('feature_address') == '4'
        new_cb = ET.Element(cb.tag, cb.attrib)
        new_cb.set('feature_address', hack_feature_adress)
        new_cb.text = cb.text
        new_cb.tail = cb.tail

        for child in cb:
            if child.tag != 'mux':
                new_cb.append(copy.deepcopy(child))
            else:
                assert len(child.keys()) == 1, "Can't hack this fabric"
                assert 'snk' in child.keys(), "Can't hack this fabric"
                new_mux = ET.Element(child.tag, {'snk' : hack_port})
                new_mux.text = child.text
                new_mux.tail = child.tail
                for src in child:
                    assert src.tag == 'src', "Can't hack this fabric"
                    new_src = copy.deepcopy(src)
                    new_src.text = src.text[:9] + str(int(src.text[9]) + 1) + src.text[10:]
                    new_mux.append(new_src)
                new_cb.append(new_mux)
        tile.append(new_cb)
    tree.write(ofile)

if __name__ == '__main__':
    import sys
    hack(*sys.argv[1:])

