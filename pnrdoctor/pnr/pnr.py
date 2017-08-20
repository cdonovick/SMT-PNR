import itertools as it

from smt_switch import smt

from pnrdoctor.smt.solvers import Solver_monosat
from pnrdoctor.util import BiMultiDict, BiDict

''' Class for handling place & route '''
class PNR:
    def __init__(self, fabric, design, solver_str, seed=1):
        self._fabric = fabric
        self._design = design

        self._place_state = BiMultiDict()
        self._route_state = BiMultiDict()

        self._place_vars = BiDict()
        self._route_vars = BiDict()

        self._place_solver = smt(solver_str)
        self._route_solver = Solver_monosat()

        # set options
        self._place_solver.SetOption('produce-models', 'true')
        self._place_solver.SetOption('random-seed', seed)
        self._place_solver.SetLogic('QF_BV')
        self._route_solver.set_option('random-seed', seed)

    def pin_module(self, module, placement):
        self._place_state[module] = placement

    def pin_tie(self, tie, placement):
        pass

    def place_design(self, funcs, model_reader):
        constraints = []
        for f in funcs:
            c = f(self.fabric, self.design, self._place_state, self._place_vars, self._place_solver)
            self._place_solver.Assert(c)

        if not self._place_solver.CheckSat():
            self._place_solver.Reset()
            # set options
            self._place_solver.SetOption('produce-models', 'true')
            self._place_solver.SetLogic('QF_BV')
            self._place_vars = BiDict()
            return False

        model_reader(self.fabric, self.design, self._place_state, self._place_vars, self._place_solver)

        return True


    def route_design(self, funcs, model_reader):
        constraints = []
        # hacky hardcoding layers
        for layer in {1, 16}:
            for f in funcs:
                c = f(self.fabric, self.design, self._place_state, self._route_state, self._route_vars, self._route_solver, layer)
                self._route_solver.add(self._route_solver.And(c))

        if not self._route_solver.solve():
            self._route_solver.reset()
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


