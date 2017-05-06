#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Place PCB using MILP

import argparse
import design, fabric, pnr, smt

from functools import partial

def main():
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='Place PCB design.')
    parser.add_argument('infile')
    parser.add_argument('--solver', type=str, default='gurobi')
    parser.add_argument('--limit', type=float, default=None)
    args = parser.parse_args()

    POSITION_T = partial(smt.MILP, solver=pnr.MILP_SOLVER(args.solver))
    PLACE_CONSTRAINTS = [pnr.init_positions(POSITION_T), 
                         pnr.distinct, 
                         pnr.inBorder]
    if args.limit is not None:
        PLACE_CONSTRAINTS.append(pnr.semiPerim(args.limit))

    d = design.Design(*design.json2graph.load_json(args.infile))
    f = fabric.parseJSON(args.infile) 

    p = pnr.PNR(f, d)

    if p.place_design(PLACE_CONSTRAINTS, pnr.place_model_reader):
        print("success!")
    else:
        raise Exception('Could not place design.')

    p.write_design(pnr.write_json(args.infile))

if __name__ == '__main__':
    main()
