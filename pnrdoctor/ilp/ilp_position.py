class ILPPosition:
    def __init__(self, name, fabric, solver):
        self._name = name
        self._fabric = fabric
        self._solver = solver
        self._x = solver.addIntVar(name + "_x")
        self._y = solver.addIntVar(name + "_y")
        self._c = solver.addIntVar(name + "_color")

    @property
    def name(self):
        return self._name

    @property
    def fabric(self):
        return self._fabric

    @property
    def solver(self):
        return self._solver

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @property
    def c(self):
        return self._c

    def encode_x(self, px):
        return px

    def encode_y(self, py):
        return py

    def encode_c(self, pc):
        return pc

    def encode(self, p):
        return tuple(p)

    @property
    def invariants(self):

        # SCIP constraints
        # self.solver.model.chgVarLb(self._x, 0)
        # self.solver.model.chgVarLb(self._y, 0)
        # self.solver.model.chgVarLb(self._c, 0)
        # self.solver.model.chgVarUb(self._x, self.fabric.cols - 1)
        # self.solver.model.chgVarUb(self._y, self.fabric.rows - 1)
        # self.solver.model.chgVarUb(self._c, self.fabric.num_tracks - 1)
        # return []

        c = []
        c.append(self._x <= self.fabric.cols-1)
        c.append(self._x >= 0)
        c.append(self._y <= self.fabric.rows-1)
        c.append(self._y >= 0)
        c.append(self._c <= self.fabric.num_tracks - 1)
        c.append(self._c >= 0)
        return c


    def get_coordinates(self):
        return (self.solver.getVal(self._x), self.solver.getVal(self._y))

    def get_color(self):
        return self.solver.getVal(self._c)
