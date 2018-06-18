from pnrdoctor.design.module import Resource
from pnrdoctor.fabric.fabricutils import trackindex


def place_model_reader(region, fabric, design, state, vars, solver):
    for module, var_d in vars.items():
        r = state[module]
        pos = {d : v.value for d,v in var_d.items() if d in r.position}
        r.set_position(pos)
        cat = {d : v.value for d,v in var_d.items() if d in r.category}
        if fabric.io_groups_dim in cat:
            cat[fabric.io_groups_dim] = fabric.group_map.I[cat[fabric.io_groups_dim]]
        r.set_category(cat)

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
            # when simultaneous, the registers have extra nodes on end
            if simultaneous and tie.src.resource == Resource.Reg:
                l = l[1:]
            if simultaneous and tie.dst.resource == Resource.Reg:
                l = l[:-1]

            path = tuple(graph.names[node] for node in l)
            # record for debug printing
            r_state[(tie, 'debug')] = path

            for n1, n2 in zip(l, l[1:]):
                edge = graph.getEdge(n1, n2)
                track = vars[edge]

                if track.dst in invariant_check:
                    assert tie.src == invariant_check[track.dst], '{} driven by {} and {}'.format(track.dst, invariant_check[track.dst].name, tie.src.name)

                invariant_check[track.dst] = tie.src
                dst = track.dst
                r_state[tie] = trackindex(snk=dst.index, src=track.src.index, bw=tie.width)

    return _route_model_reader
