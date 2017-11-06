import itertools as it
import sys

from smt_switch import smt

from pnrdoctor.design.module import Resource
from pnrdoctor.smt.region import Region
from pnrdoctor.smt.region import SYMBOLIC
from pnrdoctor.util import BiMultiDict, BiDict
from collections import defaultdict, namedtuple


class PNR:
    def __init__(self, fabric, design, solver_str, seed=1):
        self._fabric = fabric
        self._design = design

        self._place_state = BiDict()
        self._route_state = BiMultiDict()

        self._place_vars = dict()
        self._route_vars = BiDict()


        self._place_solver = smt(solver_str)
        self._solver_str   = solver_str
        self._seed         = seed
        self._set_smt_options()
        self._region = fabric.region

        for module in design.modules:
            r = self._region.make_subregion(module.name)
            r.set_size({d : 0 for d in r.position})
            r.set_position({d : SYMBOLIC for d in r.position})
            r.set_category({d : SYMBOLIC for d in r.category})
            self._place_state[module] = r

    def _set_smt_options(self):
        self._place_solver.SetOption('produce-models', 'true')
        self._place_solver.SetLogic('QF_UFBV')
        self._place_solver.SetOption('random-seed', self._seed)
        if self._solver_str == 'CVC4':
            self._place_solver.SetOption('bitblast', 'eager')
            self._place_solver.SetOption('bv-sat-solver', 'cryptominisat')

    def pin_module(self, module, placement):
        raise NotImplementedError()

    def pin_tie(self, tie, placement):
        raise NotImplementedError()
    
    def build_constraints(self, funcs):
        for f in funcs:
            c = f(self.fabric, self.design, self._place_state, self._place_vars, self._place_solver)
            self._place_solver.Assert(c)

    def solve_constraints(self):
        if self._place_solver.CheckSat():
            return True
        return False

    def read_model(self, model_reader):
        model_reader(self._region, self.fabric, self.design, self._place_state, self._place_vars, self._place_solver)

    def place_design(self, funcs, model_reader):
        self.build_constraints(funcs)
        if not self.solve_constraints():
            self._place_solver.Reset()
            self._set_smt_options()
            return False

        self.read_model(model_reader)
        return True

    def route_design(self, funcs, model_reader):
        raise NotImplementedError()

    def write_design(self, model_writer):
        model_writer(self._place_state, self._route_state)

    @property
    def fabric(self):
        return self._fabric

    @property
    def design(self):
        return self._design

    @property
    def info(self):
        raise NotImplementedError()
