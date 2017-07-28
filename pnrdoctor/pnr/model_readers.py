from pnrdoctor.design.module import Resource
from pnrdoctor.fabric.fabricutils import trackindex
from .pnrutils import get_muxindices

def place_model_reader(fabric, design, state, vars, solver):
    for module, var in vars.items():
        if module.resource == Resource.Reg:
            state[module] = var.get_coordinates() + (var.get_color(),)
        else:
            state[module] = var.get_coordinates()


def route_model_reader(fabric, design, p_state, r_state, vars, solver):

    # make sure there are never two drivers of the same port
    invariant_check = dict()

    # hardcoded layers right now
    for layer in {16}:

        for net in design.physical_nets:
            graph = vars[net]

            # hacky handle only one layer at a time
            # note: won't actually need this here when
            # routing 1 bit signals
            if net.width != layer:
                continue

            for tie in net.ties:

                src_index, dst_index = get_muxindices(tie, p_state)

                src_node = vars[fabric[src_index].source]
                dst_node = vars[fabric[dst_index].sink]
                reaches = graph.reaches(src_node, dst_node)
                l = graph.getPath(reaches)
                path = tuple(graph.names[node] for node in l)
                # record for debug printing
                r_state[(tie, 'debug')] = path
                for n1, n2 in zip(l, l[1:]):
                    edge = graph.getEdge(n1, n2)
                    track = vars[edge]

                    if track in invariant_check:
                        assert tie.src == invariant_check[track.dst], '{} driven by {} and {}'.format(track.dst, invariant_check[track.dst], tie.src)

                    invariant_check[track.dst] = tie.src

                    dst = track.dst

                    # check for feedthrough
                    if hasattr(track, 'trackindices'):
                        for pindex in track.pathindices:
                            r_state[tie] = pindex
                    else:
                        r_state[tie] = pathindex(snk=dst.index, src=track.src.index, bw=layer)
