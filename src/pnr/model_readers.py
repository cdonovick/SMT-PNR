
def place_model_reader(position_type):
    def reader(fabric, design, state, vars, solver):
        m = solver.get_model()
        for module, var in vars.items():
            state[module] = position_type.get_coordinates(m, var)

    return reader


def route_model_reader(fabric, design, p_state, r_state, vars, solver):
    model = solver.get_model()
    for src in design.modules:
        for port, net in src.outputs.items():
            src_pos = p_state[src]
            dst_pos = p_state[net.dst]
            src_pe = fab[src_pos].PE
            dst_pe = fab[dst_pos].PE
            reaches = solver.g.reaches(src_pe.getPort('out'), dst_pe.getPort(port))
            l = model.getPath(reaches)
            for n1, n2 in zip(l, l[1:]):
                edge = model.getEdge(l[0], l[1])
                track = vars.I[edge]
                src_port = track.src
                dst_port = track.dst
                outname = track.names[1]
                inname = track.names[0]
                state = (src_port.x, src_port.y, track.element, outname, inname)
                r_state[net] = state
    
