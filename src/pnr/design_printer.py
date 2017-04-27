def print_placement(design):
    def printer(p_state, r_state):
        for module in design.modules:
            try:
                print("module: {} @ ({}, {})".format(module.name, *p_state[module][0]))
                print("inputs: {}".format(', '.join(d.src.name for d in module.inputs)))
                print("outputs: {}".format(', '.join(d.dst.name for d in module.outputs)))
                print()
            except KeyError:
                print("module: {} is not placed".format(module.name))

        for net in design.nets:
            print("{} -> {}".format(net.src.name, net.dst.name))

    return printer
