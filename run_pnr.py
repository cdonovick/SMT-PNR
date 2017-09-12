#!/usr/bin/env python3
import sys
from pnrdoctor import design,  pnr, smt
from functools import partial
from pnrdoctor.config import ConfigEngine
from pnrdoctor.design import core2graph
from pnrdoctor.smt.handlers import OneHotHandler, ScalarHandler

import copy


import argparse
parser = argparse.ArgumentParser(description='Run place and route')
parser.add_argument('design', metavar='<DESIGN_FILE>', help='Mapped coreir file')
parser.add_argument('fabric', metavar='<FABRIC_FILE>', help='XML Fabric file')
parser.add_argument('--coreir-libs', nargs='+', help='coreir libraries to load', dest='libs', default=())
parser.add_argument('--print', action='store_true', help='equivelent to --print-place, --print-route')
parser.add_argument('--print-place', action='store_true', dest='print_place', help='print placement information to stdout')
parser.add_argument('--print-route', action='store_true', dest='print_route', help='print routing information to stdout')
parser.add_argument('--bitstream', metavar='<BITSTREAM_FILE>', help='output CGRA configuration in bitstream')
parser.add_argument('--annotate', metavar='<ANNOTATED_FILE>', help='output bitstream with annotations')
parser.add_argument('--noroute', action='store_true')
parser.add_argument('--solver', help='choose the smt solver to use for placement', default='Z3')

args = parser.parse_args()

design_file = args.design
fabric_file = args.fabric


PLACE_CONSTRAINTS = pnr.init_regions(OneHotHandler, ScalarHandler), pnr.distinct, pnr.neighborhood(2), pnr.register_colors, pnr.pin_IO, pnr.pin_resource,
PLACE_RELAXED     = pnr.init_regions(OneHotHandler, ScalarHandler), pnr.distinct, pnr.neighborhood(4), pnr.register_colors, pnr.pin_IO, pnr.pin_resource,

simultaneous, split_regs, ROUTE_CONSTRAINTS = pnr.recommended_route_settings(relaxed=False)
simultaneous, split_regs, ROUTE_RELAXED = pnr.recommended_route_settings(relaxed=True)

print("Loading design: {}".format(design_file))
ce = ConfigEngine()
modules, ties = design.core2graph.load_core(design_file, *args.libs)
des = design.Design(modules, ties)

print("Loading fabric: {}".format(fabric_file))

pnrdone = False

iterations = 0

while not pnrdone and iterations < 10:
    fab = pnr.parse_xml(fabric_file, ce)
    p = pnr.PNR(fab, des, args.solver)
    POSITION_T = partial(smt.BVXY, solver=p._place_solver)
    print("Placing design...", end=' ')
    sys.stdout.flush()

    if p.place_design(PLACE_CONSTRAINTS, pnr.place_model_reader):
        print("success!")
        sys.stdout.flush()
    else:
        print("\nfailed with nearest_neighbor, relaxing...", end=' ')
        sys.stdout.flush()
        if p.place_design(PLACE_RELAXED, pnr.place_model_reader):
            print("success!")
            sys.stdout.flush()
        else:
            print("!!!failure!!!")
            sys.exit(1)

    if not args.noroute:
        pnr.process_regs(des, p._place_state, fab, split_regs=split_regs)
        print("Routing design...", end=' ')
        sys.stdout.flush()
        if p.route_design(ROUTE_CONSTRAINTS, pnr.route_model_reader(simultaneous)):
            print("success!")
            pnrdone = True
        else:
            print("\nfailed with dist_factor=1, relaxing...", end=' ')
            if p.route_design(ROUTE_RELAXED, pnr.route_model_reader(simultaneous)):
                print("success!")
                pnrdone = True
            else:
                print("!!!failure!!!")
    else:
        pnrdone = True

    iterations += 1

if not pnrdone:
    print('Failed to place and route in 10 iterations')
    sys.exit(1)

print('Successfully placed and routed in {} iterations'.format(iterations))

print('Loading configuration engine with placement and route info\n')

ce.load_state(p._place_state, p._route_state)

if args.bitstream:
    bit_file = args.bitstream
    print("Writing bitsream to: {}".format(bit_file))
    pnr.write_bitstream(fab, bit_file, ce, False)

if args.annotate:
    bit_file = args.annotate
    print("Writing bitsream to: {}".format(bit_file))
    pnr.write_bitstream(fab, bit_file, ce, True)


if args.print or args.print_place:
    print("\nplacement info:")
    p.write_design(pnr.write_debug(des))

if (args.print or args.print_route) and not args.noroute:
    print("\nRouting info:")
    p.write_design(pnr.write_route_debug(des))
