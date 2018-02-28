from pnrdoctor.design.module import Resource
from pnrdoctor.fabric.fabricutils import trackindex


def place_model_reader(region, fabric, design, state, vars, solver):
    for module, var_d in vars.items():
        r = state[module]
        pos = {d : v.value for d,v in var_d.items() if d in r.position}
        r.set_position(pos)
        cat = {d : v.value for d,v in var_d.items() if d in r.category}
        r.set_category(cat)

def route_model_reader(simultaneous=False):
    def _route_model_reader(fabric, design, p_state, r_state, vars, solver):

        # make sure there are never two drivers of the same port
        invariant_check = dict()
        processed_mods = set()

        rd = fabric.rows_dim
        cd = fabric.cols_dim
        td = fabric.tracks_dim

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

                # update p_state with Monosat's re-placement decisions
                ftrack = vars[graph.getEdge(l[0], l[1])]
                ltrack = vars[graph.getEdge(l[-2], l[-1])]

                newsrcpos = {rd: ftrack.src.loc[0], cd: ftrack.src.loc[1]}
                newdstpos = {rd: ltrack.dst.loc[0], cd: ltrack.dst.loc[1]}

                newsrctracknum = ftrack.src.track
                newdsttracknum = ltrack.dst.track

                # re-place and make sure modules were not placed in more than one location
                # Memories are strange because they have ports over multiple grid locations -- leave them alone
                if tie.src.resource != Resource.Mem:
                    if tie.src in processed_mods:
                        assert p_state[tie.src].position == newsrcpos, "Module {} appears to be placed in multiple locations".format(tie.src.name)
                    else:
                        p_state[tie.src].set_position(newsrcpos)
                        if newsrctracknum is not None:
                            p_state[tie.src].set_category({td: newsrctracknum})
                        processed_mods.add(tie.src)

                if tie.dst.resource != Resource.Mem:
                    if tie.dst in processed_mods:
                        assert p_state[tie.dst].position == newdstpos, "Module {} appears to be placed in multiple locations".format(tie.dst.name)
                    else:
                        p_state[tie.dst].set_position(newdstpos)
                        if newdsttracknum is not None:
                            p_state[tie.dst].set_category({td: newdsttracknum})
                        processed_mods.add(tie.dst)

            for n1, n2 in zip(l, l[1:]):
                edge = graph.getEdge(n1, n2)
                track = vars[edge]

                if track.dst in invariant_check:
                    assert tie.src == invariant_check[track.dst], '{} driven by {} and {}'.format(track.dst, invariant_check[track.dst].name, tie.src.name)

                invariant_check[track.dst] = tie.src
                dst = track.dst
                r_state[tie] = trackindex(snk=dst.index, src=track.src.index, bw=tie.width)

    return _route_model_reader
