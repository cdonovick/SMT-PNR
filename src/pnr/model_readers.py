
def place_model_reader(fabric, design, state, vars, solver):
    m = solver.get_model()
    for module, var in vars.items():
        state[module] = var.get_coordinates(m)


def route_model_reader(fabric, design, p_state, r_state, vars, solver):
    model = solver.get_model()
    for net in design.nets:
        src = net.src
        dst = net.dst

        src_pos = p_state[src][0]
        dst_pos = p_state[dst][0]
        src_pe = fabric[src_pos].PE
        dst_pe = fabric[dst_pos].PE
        reaches = solver.g.reaches(vars[src_pe.getPort(net.src_port)], vars[dst_pe.getPort(net.dst_port)])
        l = model.getPath(reaches)
        lst = [model.names[node] for node in l]
        print(lst)
        for n1, n2 in zip(l, l[1:]):
            edge = model.getEdge(n1, n2)
            track = vars.I[edge]
            src_port = track.src
            dst_port = track.dst
            outname = track.names[1]
            inname = track.names[0]
            state = (src_port.x, src_port.y, track.element.typestr, outname, inname)
            r_state[net] = state
    
