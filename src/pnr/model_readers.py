
def place_model_reader(position_type):
    def reader(fabric, design, state, vars, solver):
        m = solver.get_model()
        for module, var in vars.items():
            state[module] = position_type.get_coordinates(m, var)

    return reader

