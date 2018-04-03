import coreir
from .module import Resource, Layer
from pnrdoctor.util import SortedDict, IdentDict, SortedSet

def load_core(file, *libs):
    context = coreir.Context()
    for lib in libs:
        context.load_library(lib)

    top_module = context.load_from_file(file)
    top_def = top_module.definition
    modules = SortedDict()

    for inst in top_def.instances:
        inst_name = inst.selectpath[0]
        inst_type = inst.module.name
        namespace = inst.module.namespace.name
        modules[inst_name] = {
            'type'  : None,
            'res'   : Resource.UNSET,
            'layer' : Layer.UNSET,
            'conf'  : None,
        }

        if namespace == 'cgralib' and inst_type == 'PE':
            modules[inst_name]['type'] = 'PE'
            modules[inst_name]['res']  = Resource.PE
            modules[inst_name]['conf'] = dict()
            op_kind = inst.module.generator_args['op_kind'].value

            if op_kind in ('alu', 'combined'):
                modules[inst_name]['layer'] |= Layer.Combined
                modules[inst_name]['conf']['alu_op'] = inst.config['alu_op'].value

            if op_kind in ('bit', 'combined'):
                modules[inst_name]['layer'] |= Layer.Combined
                modules[inst_name]['conf']['lut_value'] = inst.config['lut_value'].value.val

            if op_kind not in ('bit', 'alu', 'combined'):
                raise ValueError("Unkown op_kind `{}' in `{}' expected <`bit', `alu', `combined'>".format(file, op_kind))

        elif namespace == 'cgralib' and  inst_type == 'Mem':
            modules[inst_name]['type']  = 'Mem'
            modules[inst_name]['res']   = Resource.Mem
            modules[inst_name]['layer'] = Layer.Combined
            modules[inst_name]['conf']  = {
                        'mode'         : inst.config['mode'].value,
                        'depth'        : inst.config['depth'].value,
                        'almost_count' : inst.config['almost_count'].value,
                        'tile_en'      : inst.config['tile_en'].value,
                        'chain_enable' : inst.config['chain_enable'].value,
           }

        elif namespace == 'coreir' and inst_type == 'reg':
            modules[inst_name]['type']  = 'Reg'
            modules[inst_name]['res']   = Resource.Reg
            modules[inst_name]['layer'] = Layer.Data
            modules[inst_name]['conf']  = None
        elif namespace == 'corebit' and inst_type == 'reg':
            modules[inst_name]['type']  = 'BitReg'
            modules[inst_name]['res']   = Resource.Reg
            modules[inst_name]['layer'] = Layer.Bit
            modules[inst_name]['conf']  = None

        elif namespace == 'coreir' and inst_type == 'const':
            modules[inst_name]['type']  = 'Const'
            modules[inst_name]['res']   = Resource.Fused # always fuse constants
            modules[inst_name]['layer'] = Layer.Data
            modules[inst_name]['conf']  = inst.config['value'].value.val
        elif namespace == 'corebit' and inst_type == 'const':
            modules[inst_name]['type']  = 'Const'
            modules[inst_name]['res']   = Resource.Fused # always fuse constants
            modules[inst_name]['layer'] = Layer.Bit
            modules[inst_name]['conf']  = inst.config['value'].value

        elif namespace == 'cgralib' and inst_type == 'IO':
            modules[inst_name]['type']  = 'IO'
            modules[inst_name]['res']   = Resource.IO
            modules[inst_name]['layer'] = Layer.Data
            modules[inst_name]['conf']  = inst.config['mode'].value
        elif namespace == 'cgralib' and inst_type == 'BitIO':
            modules[inst_name]['type']  = 'BitIO'
            modules[inst_name]['res']   = Resource.IO
            modules[inst_name]['layer'] = Layer.Bit
            modules[inst_name]['conf']  = inst.config['mode'].value

        else:
            raise ValueError("Unknown namespace {} or module {} in {}".format(namespace, inst_type, file))


    ties = SortedSet()
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
        'data.in.0' : 'data0',
        'data.in.1' : 'data1',
        'data.in.2' : 'data2',
        'data.out'  : 'pe_out_res',
        'bit.in.0'  : 'bit0',
        'bit.in.1'  : 'bit1',
        'bit.in.2'  : 'bit2',
        'bit.out'   : 'pe_out_res_p',
    },

    'Const' : {
        'out' : 'out',
    },

    'IO' : {
        'in'  : 'out',
        'out' : 'in',
    },

    'BitIO' : {
        'in'  : 'bit0',
        'out' : 'pe_out_res_p',
    },

    'Reg' : {
        'in'  : 'in',
        'out' : 'out',
    },

    'BitReg' : {
        'in'  : 'in',
        'out' : 'out',
    },

    'Mem' : IdentDict(),
}


