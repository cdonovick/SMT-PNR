from design.module import Resource
from .pnrutils import get_muxindices
from fabric.fabricutils import trackindex


def place_model_reader(fabric, design, state, vars, solver):
    for module, var in vars.items():
        if module.resource == Resource.Reg:
            state[module] = var.get_coordinates() + (var.get_color(),)
        else:
            state[module] = var.get_coordinates()


def route_model_reader(fabric, design, p_state, r_state, vars, solver):

    # hardcoded layers right now
    for layer in {16}:

        for net in design.physical_nets:
            # hacky handle only one layer at a time
            # note: won't actually need this here when
            # routing 1 bit signals
            if net.width != layer:
                continue

            src_index, dst_index = get_muxindices(net, p_state)

            graph = vars[net]

            src_node = vars[fabric[src_index].source]
            dst_node = vars[fabric[dst_index].sink]
            reaches = graph.reaches(src_node, dst_node)
            l = graph.getPath(reaches)
            path = tuple(graph.names[node] for node in l)
            # record for debug printing
            r_state[(net, 'debug')] = path
            for n1, n2 in zip(l, l[1:]):
                edge = graph.getEdge(n1, n2)
                track = vars[edge]
                dst = track.dst
                r_state[net] = trackindex(snk=dst.index, src=track.src.index, bw=layer)
