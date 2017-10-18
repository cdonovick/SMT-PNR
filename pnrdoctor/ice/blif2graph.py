import sys
from collections import OrderedDict
from functools import partial

from .fabric import Fabric
from pnrdoctor.util import BiMultiDict, smart_open

Resource = Fabric.Resource

MODEL_DICT = {
    '.inputs'  : [],
    '.outputs' : [],
    '.names'  : [],
    '.gate'   : {},
    '.attr'   : {},
    '.param'  : {},
    'NETS'    : {},
}



IO_DICT = OrderedDict([
    ('PACKAGE_PIN'       , None),
    ('LATCH_INPUT_VALUE' , None),
    ('CLOCK_ENABLE'      , None),
    ('INPUT_CLK'         , None),
    ('OUTPUT_CLK'        , None),
    ('OUTPUT_ENABLE'     , None),
    ('D_OUT_0'           , None),
    ('D_OUT_1'           , None),
    ('D_IN_0'            , None),
    ('D_IN_1'            , None),
])

LC_DICT = {
    'I0'   : None,
    'I1'   : None,
    'I2'   : None,
    'I3'   : None,
    'CIN'  : None,
    'CLK'  : None,
    'CEN'  : None,
    'SR'   : None,
    'LO'   : None,
    'O'    : None,
    'COUT' : None,
}

GATE_DICT = {
    'type'   : None,
    'config' : None,
}

D_DICT = {
    'SB_IO' : IO_DICT,
    'ICESTORM_LC' : LC_DICT,
}

IO_KEYS = {
    'SB_IO' : {
        'inputs'  : ['D_OUT_0', 'D_OUT_1',],
        'outputs' : ['D_IN_0', 'D_IN_1',],
   },
    'ICESTORM_LC' : {
        'inputs'  : ['I0', 'I1', 'I2', 'I3',],
        'outputs' : ['LO', 'O', 'COUT'],
    },
}

def load_blif(file_name):
    models = {}
    nets = []
    m = None
    g = None
    # load the file into a bunch of insane dictionaries
    with open(file_name, 'r') as file:
        for line in file:
            line=line.strip().split()
            if not line:
                continue
            cmd = line[0]
            args = line[1:]
            if cmd[0] == '#':
                continue

            elif cmd  == '.model':
                assert m is None
                assert len(args) == 1
                m = args[0]
                models[m] = MODEL_DICT.copy()

            elif cmd in ('.inputs', '.outputs', '.names'):
                assert m is not None
                models[m][cmd] = args

            elif cmd == '.gate':
                assert m is not None
                assert len(args) >= 1
                g = 0 if g is None else g + 1
                models[m][cmd][g] = GATE_DICT.copy()
                d = models[m][cmd][g]
                d['type'] = args[0]
                d['config'] = D_DICT[args[0]].copy()

                for arg in args[1:]:
                    opt,val = arg.split('=')
                    assert opt in d['config'], opt
                    d['config'][opt] = val

            elif cmd == '.attr' or cmd == '.param':
                assert m is not None
                assert g is not None
                assert args
                models[m][cmd].setdefault(g, []).append(args)
            elif cmd == '.end':
                assert m is not None
                assert not args
                m = None
                g = None

            else:
                raise ValueError("Don't know how to parse line starting with: {}".format(cmd))

    # build nets into insane dictionaries
    for m, d in models.items():
        for k in ('outputs', 'inputs'):
            for g_idx, g_dict in d['.gate'].items():
                g_type = g_dict['type']
                g_config = g_dict['config']
                for port in IO_KEYS[g_type][k]:
                    n = g_config[port]
                    if n:
                        if n == '$false' or n == '$true':
                            continue

                        if n not in d['NETS']:
                            assert k == 'outputs'
                            d['NETS'][n] = [(g_idx, port, g_type)]
                        else:
                            assert k == 'inputs'
                            d['NETS'][n].append((g_idx, port, g_type))

    modules = dict() # basically the same as core2graph
    nets = BiMultiDict()  # (src_name, src_port, dst_name, dst_port, width==1) -> net_name

    # build sane module dictionary
    for m, d in models.items():
        for g_idx, g_dict in d['.gate'].items():
            g_type = g_dict['type']
            g_config = g_dict['config']
            inst_name = '{}_{}_{}'.format(m,g_idx,g_type)
            g_key = '.gate ' + g_type
            modules[inst_name] = {
                    'type'   : g_type,
                    'res'    : Resource.from_str(g_type),
                    'blif'   : {
                        g_key    : g_config,
                        '.attr'  : d['.attr'].setdefault(g_idx, None),
                        '.param' : d['.param'].setdefault(g_idx, None),
                    }
            }

    # build sane net dictionary
    for m, d in models.items():
        for n_name, l in d['NETS'].items():
            src_idx, src_port, src_type = l[0]
            src_name = '{}_{}_{}'.format(m,src_idx, src_type)

            for (dst_idx, dst_port, dst_type) in l[1:]:
                dst_name = '{}_{}_{}'.format(m,dst_idx, dst_type)
                nets[n_name] = (src_name, src_port, dst_name, dst_port, 1)



    return modules, nets

def write_blif(design, output=sys.stdout):
    return partial(_write_blif, design, output)


def _write_blif(design, output, p_state, r_state):
    with smart_open(output, 'w') as f:
        f.write('# arachne-pnr 0.1+217+0 (git sha1 c07ecb5, g++ 7.2.0-8 -O2)\n')
        f.write('.model main\n')
        f.write('.inputs I\n')
        f.write('.outputs O\n')
        f.write('.names $false\n')
        for module in design.modules:
            pos = {d.name : v for d,v in p_state[module].position.items() if v is not None}
            pos.update({d.name : v for d,v in p_state[module].category.items() if v is not None} )
            for k,v in module.blif.items():
                if v is None:
                    continue
                f.write(k)
                if isinstance(v, dict):
                    for i, j in v.items():
                        f.write(' {}={}'.format(i,j))
                    f.write('\n')
                    f.write('.attr loc "{},{}/{}"'.format(pos['col'], pos['row'], pos['lut'],))
                elif isinstance(v, list):
                    f.write(' ')
                    f.write(' '.join(v[0]))
                else:
                    assert 0,v
                f.write('\n')

                #f.write("module: {} @ {})\n".format(module.name, pos))

            #f.write("inputs: {}\n".format(', '.join(d.src.name for d in module.inputs.values())))
            #f.write("outputs: {}\n".format(', '.join(d.dst.name for d in module.outputs.values())))
            #f.write("\n")
        f.write('.end')



if __name__ == '__main__':
    import sys
    load_blif(sys.argv[1])
