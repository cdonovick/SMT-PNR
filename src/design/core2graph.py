import coreir

PORT_TRANSLATION = {
        'in0' : 'a',
        'in1' : 'b',
        'out' : 'out',
}



def load_core(file):
    mods = dict()
    ops = dict()

    c = coreir.Context()
    m = c.load_from_file(file)
    d = m.get_definition()
    l = d.get_instances()
    for i in l:
        src_op_val = ''
        src_op_atr = dict()
        if i.module_name()[0:2] == 'PE':
            s = i.select('out')
            src_name, src_port = s.get_ancestors()
            src_op = i.get_config_value('op')
            if src_op == 'const':
                src_op_val = str(i.get_config_value('constvalue'))
            out_edges = s.get_connected_wireables()
        elif i.module_name()[0:4] == 'IOIn':
            s = i.select('out')
            src_name, src_port = s.get_ancestors()
            src_op = 'io'
            src_op_atr['name'] = src_name
            src_op_atr['type'] = 'source'
            out_edges = s.get_connected_wireables()
        elif i.module_name()[0:5] == 'IOOut':
            src_port = 'out'
            src_name = i.get_ancestors()[0]
            src_op_atr['name'] = src_name
            src_op_atr['type'] = 'sink'
            src_op = 'io'
            out_edges = []
        else:
            raise ValueError('Unknown module type: {}'.format(i.module_name()))
        
        src_port = PORT_TRANSLATION[src_port]
        
        src = src_name, src_port
        mods[src] = []
        ops[src_name] = src_op, src_op_val, src_op_atr

        for w in out_edges:
            dst_name, dst_port = w.get_ancestors()
            dst_port = PORT_TRANSLATION[dst_port]
            mods[src].append((dst_name, dst_port, 16))

    return mods, ops
