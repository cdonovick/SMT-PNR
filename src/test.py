#!/usr/bin/env python3
import sys
import design, design.core2graph, fabric, pnr, smt
from functools import partial

import argparse
parser = argparse.ArgumentParser(description='Run place and route')
parser.add_argument('design', metavar='<DESIGN_FILE>', help='Mapped coreir file')
parser.add_argument('fabric', metavar='<FABRIC_FILE>', help='XML Fabric file')
parser.add_argument('--coreir-libs', nargs='+', help='coreir libraries to load', dest='libs', default=())
#parser.add_argument('--xml', nargs=2, metavar=('<PLACEMENT_FILE>', '<IO_FILE>'), help='output CGRA configuration in XML file with IO info')
parser.add_argument('--print', action='store_true', help='equivelent to --print-place, --print-route')
parser.add_argument('--print-place', action='store_true', dest='print_place', help='print placement information to stdout')
parser.add_argument('--print-route', action='store_true', dest='print_route', help='print routing information to stdout')
parser.add_argument('--bitstream', metavar='<BITSTREAM_FILE>', help='output CGRA configuration in bitstream')
parser.add_argument('--annotate', metavar='<ANNOTATED_FILE>', help='output bitstream with annotations')
parser.add_argument('--noroute', action='store_true')
args = parser.parse_args()

design_file = args.design
fabric_file = args.fabric


POSITION_T = partial(smt.BVXY, solver=pnr.PLACE_SOLVER)
PLACE_CONSTRAINTS = pnr.init_positions(POSITION_T), pnr.distinct, pnr.nearest_neighbor, pnr.pin_IO, pnr.register_colors
PLACE_RELAXED =  pnr.init_positions(POSITION_T), pnr.distinct, pnr.pin_IO, pnr.register_colors
ROUTE_CONSTRAINTS = pnr.build_msgraph, pnr.reachability, pnr.excl_constraints, pnr.dist_limit(1) 
# To use multigraph encoding:
# Note: This encoding does not handle fanout for now
# Once nets represent the whole tree of connections, this will be fixed
# ROUTE_CONSTRAINTS = pnr.build_net_graphs, pnr.reachability, pnr.dist_limit(1)

print("Loading design: {}".format(design_file))
modules, nets = design.core2graph.load_core(design_file, *args.libs)
des = design.Design(modules, nets)

print("Loading fabric: {}".format(fabric_file))
fab = fabric.pre_place_parse_xml(fabric_file)

p = pnr.PNR(fab, des)

pnrdone = False

iterations = 0

while not pnrdone and iterations < 10:
    print("Placing design...", end=' ')
    if p.place_design(PLACE_CONSTRAINTS, pnr.place_model_reader):
        print("success!")
    else:
        print("\nfailed with nearest_neighbor, relaxing...", end = ' ')
        if p.place_design(PLACE_RELAXED, pnr.place_model_reader):
            print("success!")
        else:
            print("!!!failure!!!")

    fabric.parse_xml(fabric_file, p._fabric, p._design, p._place_state)

    if not args.noroute:
        print("Routing design...", end=' ')
        if p.route_design(ROUTE_CONSTRAINTS, pnr.route_model_reader):
            print("success!")
            pnrdone = True
        else:
            print("!!!failure!!!")

    iterations += 1

if not pnrdone:
    print('Failed to place and route in 10 iterations')
    sys.exit(1)

print('Successfully placed and routed in {} iterations'.format(iterations))

if args.bitstream:
    bit_file = args.bitstream
    print("Writing bitsream to: {}".format(bit_file))
    p.write_design(pnr.write_bitstream(fabric_file, bit_file, False))

if args.annotate:
    bit_file = args.annotate
    print("Writing bitsream to: {}".format(bit_file))
    p.write_design(pnr.write_bitstream(fabric_file, bit_file, True))



if args.print or args.print_place:
    print("\nPlacement info:")
    p.write_design(pnr.write_debug(des))

if args.print or args.print_route:
    print("\nRouting info:")
    p.write_design(pnr.write_route_debug(des))
