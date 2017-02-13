import pygraphviz as pgv
import re

#For use with global_router
#accepts paths as strings with prepended locations
#done automatically in global_router.test

__bias_amount = 0.5
__name_start_index = 5
__scale_factor = 250
__cutoff = 10

def generate_dot(fab_dims, CLBs, CBr, CBb, SB, paths, filename):
    G = pgv.AGraph(name=filename, directed=True)
    #G.node_attr['fixedsize']='true'
    G.node_attr['shape'] = 'box'
    create_all_CLBs(fab_dims, CLBs, G)
    for cb in CBr:
        pos, name = parse_name(cb, (__bias_amount,0))
        G.add_node(name)
        n = G.get_node(name)
        n.attr['pos'] = '{},{}!'.format(__scale_factor*pos[0], __scale_factor*pos[1])
    for cb in CBb:
        pos, name = parse_name(cb, (0,__bias_amount))
        G.add_node(name)
        n = G.get_node(name)
        n.attr['pos'] = '{},{}!'.format(__scale_factor*pos[0], __scale_factor*pos[1])
    for s in SB:
        pos, name = parse_name(s, (__bias_amount,__bias_amount))
        G.add_node(name)
        n = G.get_node(name)
        n.attr['pos'] = '{},{}!'.format(__scale_factor*pos[0], __scale_factor*pos[1])

    #now make connections
    for path in paths:
        for i in range(0, len(path)-1):
            if len(path[i]) > __cutoff:
                n1 = path[i][0:__cutoff+1]
            else:
                n1 = path[i]
            if len(path[i+1]) > __cutoff:
                n2 = path[i+1][0:__cutoff+1]
            else:
                n2 = path[i+1]
            G.add_edge(n1, n2)

    #write to file
    G.write(filename)


def create_all_CLBs(fab_dims, CLBs, G):
    for i in range(0, fab_dims[0]):
        for j in range(0, fab_dims[1]):
            if (i,j) in CLBs:
                if len(CLBs[(i,j)]) > __cutoff:
                    name = CLBs[(i,j)][0:__cutoff+1]
                else:
                    name = CLBs[(i,j)]
                G.add_node(name)
                n = G.get_node(name)
                n.attr['style'] = 'filled'
                n.attr['fillcolor'] = '#468f05'
            else:
                name = 'CLB({},{})'.format(i,j)
                G.add_node(name)
                n = G.get_node(name)
            n.attr['pos'] = '{},{}!'.format(__scale_factor*i,__scale_factor*j)

def parse_name(node, bias):
    p = re.findall('\d+', node)
    return (int(p[0]) + bias[0], int(p[1]) + bias[1]), node
