from pnrdoctor.design.module import Resource
from pnrdoctor.fabric.fabricutils import trackindex
from .pnrutils import get_muxindices

def place_model_reader(fabric, design, state, vars, solver):
    for module, var in vars.items():
        if module.resource == Resource.Reg:
            state[module] = var.get_coordinates() + (var.get_color(),)
        else:
            state[module] = var.get_coordinates()


def route_model_reader(simultaneous=False):
    def _route_model_reader(fabric, design, p_state, r_state, vars, solver):

        # make sure there are never two drivers of the same port
        invariant_check = dict()

        processed_mods = set()

        for tie in design.ties:
            graph = solver.graphs[tie.width]

            src_node = vars[(tie.src, tie.src_port)]
            dst_node = vars[(tie.dst, tie.dst_port)]
            reaches = graph.reaches(src_node, dst_node)
            l = graph.getPath(reaches)
            assert l is not None, tie
            path = tuple(graph.names[node] for node in l)
            # record for debug printing
            r_state[(tie, 'debug')] = path

            # when simultaneous, the edges on the end are virtual
            if simultaneous:
                l = l[1:-1]
                ftrack = vars[graph.getEdge(l[0], l[1])]
                ltrack = vars[graph.getEdge(l[-2], l[-1])]

                newsrcpos = ftrack.src.loc + ((ftrack.src.track,) if ftrack.src.track is not None else tuple())
                newdstpos = ltrack.dst.loc + ((ltrack.dst.track,) if ltrack.dst.track is not None else tuple())

                # make sure modules were not placed in more than one location
                if tie.src in processed_mods:
                    assert p_state[tie.src][0] == newsrcpos, "Module {} appears to be placed in multiple locations".format(tie.src)
                else:
                    del p_state[tie.src]
                    p_state[tie.src] = newsrcpos
                    processed_mods.add(tie.src)

                if tie.dst in processed_mods:
                    assert p_state[tie.dst][0] == newdstpos, "Module {} appears to be placed in multiple locations".format(tie.dst)
                else:
                    del p_state[tie.dst]
                    p_state[tie.dst] = newdstpos
                    processed_mods.add(tie.dst)

            for n1, n2 in zip(l, l[1:]):
                edge = graph.getEdge(n1, n2)
                track = vars[edge]

                if track in invariant_check:
                    assert tie.src == invariant_check[track.dst], '{} driven by {} and {}'.format(track.dst, invariant_check[track.dst], tie.src)

                invariant_check[track.dst] = tie.src
                dst = track.dst
                r_state[tie] = trackindex(snk=dst.index, src=track.src.index, bw=tie.width)

    return _route_model_reader
