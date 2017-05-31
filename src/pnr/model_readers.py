def place_model_reader(fabric, design, state, vars, solver):
    for module, var in vars.items():
        if module.resource == 'Reg':
            state[module] = var.get_coordinates() + (var.get_color(),)
        else:
            state[module] = var.get_coordinates()


def route_model_reader(fabric, design, p_state, r_state, vars, solver):
    sources = fabric[16].sources
    sinks = fabric[16].sinks

    for net in design.virtual_nets:
        src = net.src
        dst = net.dst
        src_port = net.src_port
        dst_port = net.dst_port

        graph = vars[net]

        src_pos = p_state[src][0]
        dst_pos = p_state[dst][0]
        src_pe = sources[src_pos + (src_port,)]
        dst_pe = sinks[dst_pos + (dst_port,)]
        reaches = graph.reaches(vars[src_pe], vars[dst_pe])
        l = graph.getPath(reaches)
        path = tuple(graph.names[node] for node in l)
        # record for debug printing
        r_state[(net, 'debug')] = path
        for n1, n2 in zip(l, l[1:]):
            edge = graph.getEdge(n1, n2)
            track = vars[edge]
            src = track.src
            outname = track.track_names[1]
            inname = track.track_names[0]
            state = (src.x, src.y, track.parent, outname, inname)
            r_state[net] = state
