#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Place PCB using MILP

import json
import argparse
import design, fabric, pnr, smt, design.json2graph

from functools import partial
from design.module import RectShape

def main():
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='Place PCB design.')
    parser.add_argument('infile')
    parser.add_argument('outfile')
    parser.add_argument('--solver', type=str, default='gurobi')
    args = parser.parse_args()

    # Instantiate the placement problem
    f = fabric.parseJSON(args.infile) 
    d = design.Design(*design.json2graph.load_json(args.infile))
    place_solver = pnr.SolverMILP(args.solver)

    p = pnr.PNR(f, d, 
                place_solver=place_solver, 
                placement_type=smt.PcbPlacement)

    # Define the placement constraints
    place_constraints = [
                         pnr.invariants,
                         pnr.pinned,
                         pnr.distinct,
                         pnr.inFabric
                        ]

    # TODO: infer this automatically
    place_solver.BigM = max(f.width, f.height)

    # Try to place the design
    result = p.place_design(place_constraints, pnr.place_model_reader)

    if result:
        print('Success!')
    else:
        raise Exception('Could not place design.')

    # Organize placements by module name
    placements = {}
    for module, placement in p.place_state.items():
        name = module.name.split('_')[0]
        placements[name] = placement
    
    # Load original design from JSON
    with open(args.infile, 'r') as f:
        json_dict = json.load(f)

    # Update certain entries in the dictionary
    for module in json_dict['modules']:
        name = module['reference']
        module['x'] = placements[name].position[0]
        module['y'] = placements[name].position[1]
        module['theta'] = placements[name].rotation
    
    # Write design to file
    with open(args.outfile, 'w') as f:
        json.dump(json_dict, f, indent=2, sort_keys=True)
    
if __name__ == '__main__':
    main()
