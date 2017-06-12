import coreir
from .module import Resource
from util import SortedDict

def load_core(file, *libs):
    context = coreir.Context()
    for lib in libs:
        context.load_library(lib)

    top_module = context.load_from_file(file)
    top_def = top_module.definition
    modules = SortedDict()

    for inst in top_def.instances:
        inst_name = inst.selectpath[0]
        inst_type = inst.module_name

        modules[inst_name] = dict()

        if inst_type[:2] == 'PE':
            modules[inst_name]['type'] = 'PE'
            modules[inst_name]['conf'] = inst.get_config_value('op')
            modules[inst_name]['res']  = Resource.PE

        elif inst_type[:5] == 'Const':
            modules[inst_name]['type'] = 'Const'
            modules[inst_name]['conf'] = inst.get_config_value('value')
            modules[inst_name]['res']  = Resource.UNSET

        elif inst_type[:2] == 'IO':
            modules[inst_name]['type'] = 'IO'
            modules[inst_name]['conf'] = inst.get_config_value('mode')
            modules[inst_name]['res']  = Resource.IO

        elif inst_type[:3] == 'Reg':
            modules[inst_name]['type'] = 'Reg'
            modules[inst_name]['conf'] = None
            modules[inst_name]['res']  = Resource.Reg

        elif inst_type[:3] == 'Mem':
            modules[inst_name]['type'] = 'Mem'
            modules[inst_name]['conf'] = inst.get_config_value('mode')
            modules[inst_name]['res']  = Resource.Mem

        else:
            raise ValueError("Unknown module_name '{}' expected <'PE', 'Const', 'IO', 'Reg', 'Mem'>".format(inst_type))

    nets = set()
    for con in top_def.connections:
        v1 = con.first.selectpath
        v2 = con.second.selectpath

        if 'out' in v1:
            src = v1
            dst = v2
        else:
            src = v2
            dst = v1

        src_name = src[0]
        dst_name = dst[0]
        src_port = PORT_TRANSLATION[modules[src_name]['type']][','.join(src[1:])]
        dst_port = PORT_TRANSLATION[modules[dst_name]['type']][','.join(dst[1:])]
        width = 16

        net = (src_name, src_port, dst_name, dst_port, width)
        nets.add(net)


    return modules, nets



PORT_TRANSLATION = {
    'PE' : {
        'data,in,0' : 'a',
        'data,in,1' : 'b',
        'data,out'  : 'out',
        'bit,in,0'  : 'd',
    },
    'Const' : {
        'out' : 'out',
    },
    'IO' : {
        'in'  : 'a',
        'out' : 'out',
    },
    'Reg' : {
        'in'  : 'a',
        'out' : 'out',
    },
}



#def load_core(file):
#    mods = SortedDict()
#    ops = dict()
#
#    c = coreir.Context()
#    m = c.load_from_file(file)
#    d = m.get_definition()
#    l = d.get_instances()
#    for i in l:
#        src_op_val = ''
#        src_op_atr = dict()
#        if i.module_name()[0:2] == 'PE':
#            s = i.select('out')
#            src_name, src_port = s.get_ancestors()
#            src_op = i.get_config_value('op')
#            if src_op == 'const':
#                src_op_val = str(i.get_config_value('constvalue'))
#            out_edges = s.get_connected_wireables()
#        elif i.module_name()[0:4] == 'IOIn':
#            s = i.select('out')
#            src_name, src_port = s.get_ancestors()
#            src_op = 'io'
#            src_op_atr['name'] = src_name
#            src_op_atr['type'] = 'source'
#            out_edges = s.get_connected_wireables()
#        elif i.module_name()[0:5] == 'IOOut':
#            src_port = 'out'
#            src_name = i.get_ancestors()[0]
#            src_op_atr['name'] = src_name
#            src_op_atr['type'] = 'sink'
#            src_op = 'io'
#            out_edges = []
#        else:
#            raise ValueError('Unknown module type: {}'.format(i.module_name()))
#
#        src_port = PORT_TRANSLATION[src_port]
#
#        src = src_name, src_port
#        mods[src] = []
#        ops[src_name] = src_op, src_op_val, src_op_atr
#
#        for w in out_edges:
#            dst_name, dst_port = w.get_ancestors()
#            dst_port = PORT_TRANSLATION[dst_port]
#            mods[src].append((dst_name, dst_port, 16))
#
#    return mods, ops
