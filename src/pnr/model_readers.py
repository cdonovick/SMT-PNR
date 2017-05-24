
#hacky -- this is the same function as defined in pnr.constraints
def _is_placeable(x) : return x.type_ in ('PE', 'IO')

def place_model_reader(fabric, design, state, vars, solver):
    for module, var in vars.items():
        state[module] = var.get_coordinates()


def route_model_reader(fabric, design, p_state, r_state, vars, solver):
    sources = fabric.sources
    sinks = fabric.sinks
    
    for net in design.nets:
        src = net.src
        dst = net.dst
        src_port = net.src_port
        dst_port = net.dst_port
        # contract nets with unplaced modules
        # Note: This results in repeated constraints
        if not _is_placeable(src):
            assert len(src.inputs) <= 1
            if src.inputs:
                srcnet = next(iter(src.inputs.values()))
                src = srcnet.src
                src_port = srcnet.src_port
            else:
                continue

        if not _is_placeable(dst):
            assert len(dst.outputs) <= 1
            if dst.outputs:
                dstnet = next(iter(dst.outputs.values()))
                dst = dstnet.dst
                dst_port = dstnet.dst_port
            else:
                continue

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
            src_port = track.src
            outname = track.track_names[1]
            inname = track.track_names[0]
            state = (src_port.x, src_port.y, track.parent, outname, inname)
            r_state[net] = state
