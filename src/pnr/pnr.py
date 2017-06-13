from util import BiMultiDict, BiDict
from smt.solvers import Solver_z3, Solver_monosat
import itertools as it
from smt_switch import solvers


PLACE_SOLVER = solvers.Z3Solver()
_ROUTE_SOLVER = Solver_monosat()

''' Class for handling place & route '''
class PNR:
    def __init__(self, fabric, design):
        self._fabric = fabric
        self._design = design

        self._place_state = BiMultiDict()
        self._route_state = BiMultiDict()

        self._place_vars = BiDict()
        self._route_vars = BiDict()

        self._place_solver = PLACE_SOLVER
        self._route_solver = _ROUTE_SOLVER

        # set options
        self._place_solver.set_option('produce-models', 'true')

    def pin_module(self, module, placement):
        self._place_state[module] = placement

    def pin_net(self, net, placement):
        pass

    def place_design(self, funcs, model_reader):
        constraints = []
        for f in funcs:
            c = f(self.fabric, self.design, self._place_state, self._place_vars, self._place_solver)
            self._place_solver.add(c)


        if not self._place_solver.check_sat():
            self._place_solver.reset()
            # set options
            self._place_solver.set_option('produce-models', 'true')
            self._place_vars = BiDict()
            return False

        model_reader(self.fabric, self.design, self._place_state, self._place_vars, self._place_solver)

        return True


    def route_design(self, funcs, model_reader):
        constraints = []
        for f in funcs:
            # hacky hardcoding layers
            for layer in {16}:
                c = f(self.fabric, self.design, self._place_state, self._route_state, self._route_vars, self._route_solver, layer)
                self._route_solver.add(self._route_solver.And(c))

        if not self._route_solver.solve():
            self._route_solver.reset()
            self._place_state = BiMultiDict()
            self._route_vars = BiDict()
            return False


        model_reader(self.fabric, self.design, self._place_state, self._route_state, self._route_vars, self._route_solver)
        return True

    def write_design(self, model_writer):
        model_writer(self._place_state, self._route_state)

    @property
    def fabric(self):
        return self._fabric

    @property
    def design(self):
        return self._design


