#!/usr/bin/env python3
import sys
import design, design.core2graph, fabric, pnr, smt
from functools import partial

import argparse
parser = argparse.ArgumentParser(description='Run place and route')
parser.add_argument('df', metavar='<DESIGN_FILE>', help='Mapped coreir file')
parser.add_argument('ff', metavar='<FABRIC_FILE>', help='XML Fabric file')
parser.add_argument('--xml', nargs=2, metavar=('<PLACEMENT_FILE>', '<IO_FILE>'), 
    help='output CGRA configuration in XML file with IO info')
parser.add_argument('--bitstream', metavar='<BITSTREAM_FILE>', 
        help='output CGRA configuration in bitstream')
parser.add_argument('--print', action='store_true', help='print CGRA configuration to stdout')
args = parser.parse_args()

df = args.df
ff = args.ff


POSITION_T = partial(smt.Packed2H, solver=pnr.PLACE_SOLVER)
PLACE_CONSTRAINTS = pnr.init_positions(POSITION_T), pnr.distinct, pnr.nearest_neighbor, pnr.pin_IO
PLACE_RELAXED =  pnr.init_positions(POSITION_T), pnr.distinct, pnr.pin_IO
ROUTE_CONSTRAINTS = pnr.build_msgraph, pnr.excl_constraints, pnr.reachability, pnr.dist_limit(1)
# To use multigraph encoding:
# ROUTE_CONSTRAINTS = pnr.build_net_graphs, pnr.reachability, pnr.dist_limit(1)

print("Loading design: {}".format(df))
d = design.Design(*design.core2graph.load_core(df))

print("Loading fabric: {}".format(ff))
f = fabric.parseXML(ff)

p = pnr.PNR(f, d)

print("Placing design...", end=' ')
if p.place_design(PLACE_CONSTRAINTS, pnr.place_model_reader):
    print("success!")
else:
    print("\nfailed with nearest_neighbor, relaxing...", end = ' ')
    if p.place_design(PLACE_RELAXED, pnr.place_model_reader):
        print("success!")
    else:
        print("!!!failure!!!")
        sys.exit(1)

print("Routing design...", end=' ')
if p.route_design(ROUTE_CONSTRAINTS, pnr.route_model_reader):
    print("success!")
else:
    print("!!!failure!!!")
    sys.exit(1)

if args.xml:
    cf, io = args.xml
    print("Writing design to: {}".format(cf))
    print("Writing io settings to: {}".format(io))
    p.write_design(pnr.write_xml(ff, cf, io))

if args.bitstream:
    bf = args.bitstream 
    print("Writing bitsream to: {}".format(bf))
    p.write_design(pnr.write_bitstream(ff, bf))

if args.print:
    print("\nPlacement info:")
    p.write_design(pnr.write_debug(d))

