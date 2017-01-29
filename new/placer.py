import math
import os
import constraints
import design
import position
import dot2smt
import z3
import z3util as zu


class Placer:
    #TODO handle different types
    def __init__(self, fabric):
        self.fabric = fabric
        
    def parse_file(self, filepath):
        '''
        Parses the provided file using dot2smt
        '''
        filename, file_extension = os.path.splitext(filepath)
        if file_extension == '.dot':
            return dot2smt.from_file(filepath)
        else:
            raise NotImplementedError('Parsing {} files is not yet supported'.format(file_extension))

    def place(self, adj, limit=5):
        print('Creating design...')
        d = design.Design(adj, self.fabric, position.Packed2H, 'Design1')
        d.add_constraint_generator(constraints.nearest_neighbor_fast)
        d.add_constraint_generator(constraints.distinct)
        print('Initializing solver and adding constraints...')
        solver = z3.Solver()
        solver.add(d.constraints)
        counter = 0
        print('Finding satisfying model with wire_lengths = {}'.format(self.fabric.wire_lengths))
        result = solver.check()
        while result != z3.sat and counter < limit:
            print('Placement with wire_lengths = {} is unsat.'.format(self.fabric.wire_lengths))
            self.fabric.update_wire_lengths()
            print('Resetting and trying with wire_lengths = {}'.format(self.fabric.wire_lengths))
            solver.reset()
            d._reset_g_constraints()
            solver.add(d.constraints)
            counter += 1
            result = solver.check()

        if result == z3.sat:
            print('Found satisfying placement')
            return d, solver.model()
