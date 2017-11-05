import sys
from functools import partial
from pnrdoctor.util import smart_open

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

            f.write("inputs: {}\n".format(', '.join(d.src.name for d in module.ports.values())))
            

