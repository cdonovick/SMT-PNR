from util.bimdict import BiMultiDict
from smt.solvers import Solver_z3, Solver_monosat 
import itertools as it


__PLACE_SOLVER = Solver_z3
__ROUTE_SOLVER = Solver_monosat

''' Class for handling place & route '''
class PNR:
    def __init__(self, fabric, design):
        self._fabric = fabric
        self._design = design

        self._place_state = BiMultiDict()
        self._route_state = BiMultiDict()

        self._place_vars = BiMultiDict()
        self._route_vars = BiMultiDict()
        
        self._place_solver = __PLACE_SOLVER() 
        self._route_solver = __ROUTE_SOLVER()

    def pin_module(self, module, placement):
        self._place_state[module] = placement
    
    def pin_net(self, net, placement):
        pass

    def place_designs(self, initializers=(), consraint_generators=(), finalizers=(), model_reader=None):
        constraints = []
        for f in it.chain(initializers, constraint_generators, finalizers):
            c = f(self.fabric, self.design, self._place_state, self._place_vars, self._place_solver)
            self._place_solver.add(c)

        ###
        # Should inspect model and update place_state
        ###
        if not self._place_solver.solve():
            return None

        return self._place_solver.get_model()


    def route_designs(self, initializers=(), consraint_generators=(), finalizers=(), model_reader=None):
        constraints = []
        for f in it.chain(initializers, constraint_generators, finalizers):
            c = f(self.fabric, self.design, self._place_state, self._route_state, self._route_vars, self._route_solver)
            self._route_solver.add(self._route_solver.And(c))

        ###
        # Should inspect model and update route_state
        ###
        if not self._route_solver.solve():
            return None
        return self._route_solver.get_model()

    @property
    def fabric(self):
        return self._fabric

    @property
    def design(self):
        return self._design
    

