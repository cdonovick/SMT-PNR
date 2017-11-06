from copy import deepcopy
MOD_ARGS = {
    'i_ports' : [],
    'o_ports' : [],
}

CON_ARGS = {
    'module' : None,
    'port'   : None,
}

NET_ARGS = {
    'src'  : None,
    'dsts' : [],
}

def chain(n): 
    def _narg():
        args = deepcopy(NET_ARGS)
        args['src'] = deepcopy(CON_ARGS) 
        args['dsts'] = [deepcopy(CON_ARGS)]
        return args
    
    def m_name(idx):
        return '{}_m'.format(idx)

    def n_name(s, d):
        return '{}_{}_n'.format(s,d)

    def _wire(nets, idx):
        args = _narg()

        s_name = m_name(idx)
        d_name = m_name(idx+1)

        args['src']['module'] = s_name
        args['src']['port']   = 1

        args['dsts'][0]['module'] = d_name
        args['dsts'][0]['port']   = 0
        nets[n_name(idx,idx+1)] = args

    c_args = {
        'i_ports' : [0],
        'o_ports' : [1],
    }

    mods = {m_name(i) : c_args for i in range(n)}
    nets = dict()


    for i in range(n-1):
        _wire(nets, i)
    

    return mods, nets


def tree(d):
    def _narg():
        args = deepcopy(NET_ARGS)
        args['src'] = deepcopy(CON_ARGS)
        args['dsts'] = [deepcopy(CON_ARGS)]

    def _wire(nets, idx):
        args = _narg()
        args['src']['module'] = 2*idx + 1
        args['src']['port']   = 0
        args['dsts'][0]['module'] = idx
        args['dsts'][0]['port']   = 1
        nets[(2*idx+1, idx)] = args

        args = _narg()
        args['src']['module'] = 2*idx + 2
        args['src']['port']   = 0

        args['dsts'][0]['module'] = idx
        args['dsts'][0]['port']   = 2
        nets[(2*idx+2, idx)] = args




    n = 2**d - 1
    tree_args = {
        'i_ports' : [1,2],
        'o_ports' : [0],
    }

    mods = {i : tree_args for i in range(n)}
    nets = dict()
