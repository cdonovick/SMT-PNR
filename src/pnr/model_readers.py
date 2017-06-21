from design.module import Resource

def place_model_reader(fabric, design, state, vars, solver):
    for module, var in vars.items():
        if module.resource == Resource.Reg:
            state[module] = var.get_coordinates() + (var.get_color(),)
        else:
            state[module] = var.get_coordinates()


def route_model_reader(fabric, design, p_state, r_state, vars, solver):

    # hardcoded layers right now
    for layer in {16}:

        sources = fabric[layer].sources
        sinks = fabric[layer].sinks
        pnrconfig = fabric.config

        for net in design.physical_nets:
            # hacky handle only one layer at a time
            # note: won't actually need this here when
            # routing 1 bit signals
            if net.width != layer:
                continue

            src = net.src
            dst = net.dst
            src_port = net.src_port
            dst_port = net.dst_port

            graph = vars[net]

            src_index = p_state[src][0]
            dst_index = p_state[dst][0]

            # get correct tuple index
            # registers don't need their port
            if src.resource != Resource.Reg:
                src_index = src_index + (src_port,)
            if dst.resource != Resource.Reg:
                dst_index = dst_index + (dst_port,)

            src_node = vars[sources[src_index]]
            dst_node = vars[sinks[dst_index]]
            reaches = graph.reaches(src_node, dst_node)
            l = graph.getPath(reaches)
            path = tuple(graph.names[node] for node in l)
            # record for debug printing
            r_state[(net, 'debug')] = path
            for n1, n2 in zip(l, l[1:]):
                edge = graph.getEdge(n1, n2)
                track = vars[edge]
                src = track.src
                c = pnrconfig.trackconfig[track]
                state = (src.x, src.y, c[1], c[0][1], c[0][0])
                r_state[net] = state
