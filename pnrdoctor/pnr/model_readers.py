from collections import Counter

from pnrdoctor.design.module import Resource, Layer
from pnrdoctor.fabric.fabricutils import trackindex


def place_model_reader(region, fabric, design, state, vars, solver):
    for module, var_d in vars.items():
        r = state[module]
        pos = {d : v.value for d,v in var_d.items() if d in r.position}
        r.set_position(pos)
        cat = {d : v.value for d,v in var_d.items() if d in r.category}
        r.set_category(cat)

def distinct_model_reader(region, fabric, design, state, vars, solver):
    total = 0
    seen = set()
    for m1 in design.modules:
        seen.add(m1)

        for m2 in design.modules:
            if m2 in seen:
                continue
            if m1 != m2 and state[m1].parent == state[m2].parent and m1.resource == m2.resource:
                total += 1

                v1,v2 = vars[m1],vars[m2]
                s = v1.keys() & v2.keys()
                if all(not v1[d].value_distinct(v2[d]) for d in s):
                    return solver.Or([v1[d].distinct(v2[d]) for d in s])

    for module, var_d in vars.items():
        r = state[module]
        pos = {d : v.value for d,v in var_d.items() if d in r.position}
        r.set_position(pos)
        cat = {d : v.value for d,v in var_d.items() if d in r.category}
        r.set_category(cat)

    print(f'Total possible distinct constraints {total}')

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

                # TODO: Re-enable this -- update place state with monosat's adjustments
                # ftrack = vars[graph.getEdge(l[0], l[1])]
                # ltrack = vars[graph.getEdge(l[-2], l[-1])]

                # newsrcpos = ftrack.src.loc + ((ftrack.src.track,) if ftrack.src.track is not None else tuple())
                # newdstpos = ltrack.dst.loc + ((ltrack.dst.track,) if ltrack.dst.track is not None else tuple())

                # # make sure modules were not placed in more than one location
                # if tie.src in processed_mods:
                #     assert p_state[tie.src][0] == newsrcpos, "Module {} appears to be placed in multiple locations".format(tie.src)
                # else:
                #     del p_state[tie.src]
                #     p_state[tie.src] = newsrcpos
                #     processed_mods.add(tie.src)

                # if tie.dst in processed_mods:
                #     assert p_state[tie.dst][0] == newdstpos, "Module {} appears to be placed in multiple locations".format(tie.dst)
                # else:
                #     del p_state[tie.dst]
                #     p_state[tie.dst] = newdstpos
                #     processed_mods.add(tie.dst)

            for n1, n2 in zip(l, l[1:]):
                edge = graph.getEdge(n1, n2)
                track = vars[edge]

                if track.dst in invariant_check:
                    assert tie.src == invariant_check[track.dst], '{} driven by {} and {}'.format(track.dst, invariant_check[track.dst].name, tie.src.name)

                invariant_check[track.dst] = tie.src
                dst = track.dst
                r_state[tie] = trackindex(snk=dst.index, src=track.src.index, bw=tie.width)

    return _route_model_reader
