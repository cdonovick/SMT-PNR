import itertools as it

from smt_switch import smt

from pnrdoctor.design.module import Resource
from pnrdoctor.smt.region import Region
from pnrdoctor.smt.region import SYMBOLIC
from pnrdoctor.smt.solvers import Solver_monosat
from pnrdoctor.util import BiMultiDict, BiDict

''' Class for handling place & route '''
class PNR:
    def __init__(self, fabric, design, solver_str):
        self._fabric = fabric
        self._design = design

        self._place_state = BiDict()
        self._route_state = BiMultiDict()

        self._place_vars = dict()
        self._route_vars = BiDict()

        self._place_solver = smt(solver_str)
        self._route_solver = Solver_monosat()

        # set options
        self._place_solver.SetOption('produce-models', 'true')

        # set up region
        self._region = Region.from_frabic('CGRA', self.fabric)
        for module in design.modules:
            r = self._region.make_subregion(module.name)
            # kinda hackish need to make rules dictionary
            # so r.sizes can be safely mutated directly
            r.set_size({d : 0 for d in r.size})
            r.set_position({d : SYMBOLIC for d in r.position})
            for d in r.category:
                if module.resource == Resource.Reg or d != fabric.tracks_dim:
                    r.set_category({d : SYMBOLIC})

            self._place_state[module] = r

    def pin_module(self, module, placement):
        raise NotImplementedError()

    def pin_tie(self, tie, placement):
        raise NotImplementedError()

    def place_design(self, funcs, model_reader):
        constraints = []
        for f in funcs:
            c = f(self._region, self.fabric, self.design, self._place_state, self._place_vars, self._place_solver)
            self._place_solver.Assert(c)

        if not self._place_solver.CheckSat():
            #print(self._place_solver.Assertions)
            #self._place_solver.reset()
            # set options
            self._place_solver.SetOption('produce-models', 'true')
            self._place_vars = dict()
            return False

        model_reader(self._region, self.fabric, self.design, self._place_state, self._place_vars, self._place_solver)

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

