import itertools as it

from smt_switch import smt

from pnrdoctor.design.module import Resource
from pnrdoctor.smt.region import Region
from pnrdoctor.smt.region import SYMBOLIC
from pnrdoctor.smt.solvers import Solver_monosat
from pnrdoctor.util import BiMultiDict, BiDict
from pnrdoctor.ilp.ilp_solver import ilp_solvers
from collections import defaultdict, namedtuple


class PNR:
    def __init__(self, fabric, design, solver_str, seed=1):
        self._fabric = fabric
        self._design = design

        self._place_state = BiDict()
        self._route_state = BiMultiDict()

        self._place_vars = dict()
        self._route_vars = BiDict()

        self._smt_solver = True

        if solver_str in ilp_solvers:
            self._place_solver = ilp_solvers[solver_str]()
            self._smt_solver = False

        else:
            self._place_solver = smt(solver_str)
            # set options
            self._place_solver.SetOption('produce-models', 'true')
            self._place_solver.SetLogic('QF_UFBV')
            self._place_solver.SetOption('random-seed', seed)

            # use best settings per solver
            if solver_str == 'CVC4':
                self._place_solver.SetOption('bitblast', 'eager')
                self._place_solver.SetOption('bv-sat-solver', 'cryptominisat')

        self._route_solver = Solver_monosat()
        self._route_solver.set_option('random-seed', seed)

        # set up region
        self._region = fabric.region

        for module in design.modules:
            r = self._region.make_subregion(module.name)
            # kinda hackish need to make rules dictionary
            # so r.sizes can be safely mutated directly
            r.set_size({d : 0 for d in r.size})
            r.set_position({d : SYMBOLIC for d in r.position})
            r.set_category({d : SYMBOLIC for d in r.category})

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
            self._place_solver.Reset()
            # set options for smt solver
            if self._smt_solver:
                self._place_solver.SetOption('produce-models', 'true')
                self._place_solver.SetLogic('QF_BV')
                self._place_vars = BiDict()
            return False

        model_reader(self._region, self.fabric, self.design, self._place_state, self._place_vars, self._place_solver)

        return True


    def route_design(self, funcs, model_reader):
        constraints = []
        for f in funcs:
            c = f(self.fabric, self.design, self._place_state, self._route_state, self._route_vars, self._route_solver)
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

    @property
    def info(self):
        s = '\nDesign info: \n'
        for k, v in self._info.design.items():
            name = getattr(k, "name", k)
            s += "{}: {}\n".format(name, v)
        s += '\nFabric info: \n'
        for k, v in self._info.fabric.items():
            s += "{}: {}\n".format(k.name, v)

        return s
