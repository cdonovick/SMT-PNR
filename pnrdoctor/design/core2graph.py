import coreir
from .module import Resource
from pnrdoctor.util import SortedDict

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

        if inst_type == 'PE':
            modules[inst_name]['type'] = 'PE'
            modules[inst_name]['conf'] = inst.config['op'].value
            modules[inst_name]['res']  = Resource.PE

        elif inst_type == 'BitPE':
            modules[inst_name]['type'] = 'BitPE'
            modules[inst_name]['conf'] = inst.config['LUT_init'].value
            modules[inst_name]['res']  = Resource.PE

        elif inst_type == 'DataPE':
            modules[inst_name]['type'] = 'DataPE'
            modules[inst_name]['conf'] = inst.config['op'].value
            modules[inst_name]['res']  = Resource.PE

        elif inst_type.title() == 'Const':  # using title to support old and new versions of coreir for now
            modules[inst_name]['type'] = 'Const'
            modules[inst_name]['conf'] = inst.config['value'].value
            modules[inst_name]['res']  = Resource.Fused # always fuse constants

        elif inst_type == 'IO':
            modules[inst_name]['type'] = 'IO'
            modules[inst_name]['conf'] = inst.config['mode'].value
            modules[inst_name]['res']  = Resource.IO

        elif inst_type == 'bitIO':
            modules[inst_name]['type'] = 'bitIO'
            modules[inst_name]['conf'] = inst.config['mode'].value
            modules[inst_name]['res']  = Resource.IO

        elif inst_type.title() == 'Reg':
            modules[inst_name]['type'] = 'Reg'
            modules[inst_name]['conf'] = None
            modules[inst_name]['res']  = Resource.Reg

        elif inst_type == 'Mem':
            modules[inst_name]['type'] = 'Mem'
            modules[inst_name]['conf'] = {
                    'mode'              : inst.config['mode'].value,
                    'fifo_depth'        : inst.config['fifo_depth'].value,
                    'almost_full_count' : inst.config['almost_full_cnt'].value,
                    'chain_enable'      : '0', #HACK
                    'tile_en'           : '1', #HACK
            }
            modules[inst_name]['res']  = Resource.Mem

        else:
            raise ValueError("Unknown module_name `{}' in `{}' expected <`PE', `DataPE', `BitPE', `Const', `IO', `bitIO',  `Reg', `Mem'>".format(inst_type, file))


    ties = set()
    for con in top_module.directed_module.connections:
        src = con.source
        dst = con.sink

        src_name = src[0]
        dst_name = dst[0]
        src_port = _PORT_TRANSLATION[modules[src_name]['type']]['.'.join(src[1:])]
        dst_port = _PORT_TRANSLATION[modules[dst_name]['type']]['.'.join(dst[1:])]

        curr = top_def
        for select_step in src:
            curr = curr.select(select_step)

        width = curr.type.size

        tie = (src_name, src_port, dst_name, dst_port, width)
        ties.add(tie)


    return modules, ties



_PORT_TRANSLATION = {
    'PE' : {
        'data.in.0' : 'a',
        'data.in.1' : 'b',
        'data.out'  : 'pe_out_res',
        'bit.in.0'  : 'd',
        'bit.in.1'  : 'e',
        'bit.in.2'  : 'f',
        'bit.out'   : 'pe_out_p',
    },

    'BitPE' : {
        'bit.in.0'  : 'd',
        'bit.in.1'  : 'e',
        'bit.in.2'  : 'f',
        'bit.out'   : 'pe_out_p',
    },

    'DataPE' : {
        'data.in.0' : 'a',
        'data.in.1' : 'b',
        'data.out'  : 'pe_out_res',
    },

    'Const' : {
        'out' : 'out',
    },

    'IO' : {
        'in'  : 'a',
        'out' : 'pe_out_res',
    },

    'BitIO' : {
        'in'  : 'd',
        'out' : 'pe_out_p',
    },

    'Reg' : {
        'in'  : 'a',
        'out' : 'out',
    },

    'Mem' : {
        'rdata'  : 'mem_out',
        'addr'   : 'ain',
        'ren'    : 'ren',
        'empty'  : 'valid',
        'wdata'  : 'din',
        'wen'    : 'wen',
        'full'   : 'almost_full',
    },
}
