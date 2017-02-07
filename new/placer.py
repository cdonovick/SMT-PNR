import math
import os
import constraints
import design
import position
import dot2smt
import z3
import tests
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
        neighborhood = 1
        d.add_constraint_generator('neighborhood', constraints.in_neighborhood(neighborhood))
        d.add_constraint_generator('distinct', constraints.distinct)
        print('Initializing solver and adding constraints...')
        solver = z3.Solver()
        solver.add(d.constraints)
        counter = 0
        print('Finding satisfying model with neighborhood = {}'.format(neighborhood))
        result = solver.check()
        while result != z3.sat and counter < limit:
            print('Placement with neighborhood = {} is unsat.'.format(neighborhood))
            neighborhood += 1
            print('Resetting and trying with neighborhood = {}'.format(neighborhood))
            solver.reset()
            d.remove_constraint_generator('neighborhood')
            d.add_constraint_generator('neighborhood', constraints.in_neighborhood(neighborhood))
            solver.add(d.constraints)
            counter += 1
            result = solver.check()

        if result == z3.sat:
            print('Found satisfying placement')
            tests.model_printer(solver.model(), d)
            return solver.model(), d
