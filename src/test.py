#!/usr/bin/env python3
import sys
import design, design.core2graph, fabric, pnr, smt

if len(sys.argv) != 4:
    print('usage: {} <DESIGN_FILE> <FABRIC_FILE> <OUTPUT_FILE>'.format(sys.argv[0]))
    sys.exit(1)


DESIGN_FILE = sys.argv[1] 
FABRIC_FILE = sys.argv[2]
OUTPUT_FILE = sys.argv[3]

POSITION_T = smt.BVXY
PLACE_CONSTRAINTS = pnr.init_positions(POSITION_T), pnr.distinct, pnr.nearest_neighbor, pnr.pin_IO
PLACE_RELAXED =  pnr.init_positions(POSITION_T), pnr.distinct, pnr.pin_IO
ROUTE_CONSTRAINTS = pnr.build_msgraph, pnr.excl_constraints, pnr.reachability, #pnr.dist_limit(1.5)


print("Loading design: {}".format(DESIGN_FILE))
d = design.Design(*design.core2graph.load_core(DESIGN_FILE))
print("Loading fabric: {}".format(FABRIC_FILE))
f = fabric.parseXML(FABRIC_FILE)

p = pnr.PNR(f, d)

print("Placing design...", end=' ')
if p.place_design(PLACE_CONSTRAINTS, pnr.place_model_reader):
    print("success!")
else:
    print("\nfailed with nearest_neighbor, relaxing...", end = ' ')
    if p.place_design(PLACE_RELAXED, pnr.place_model_reader):
        print("success!")
    else:
        print("failure")
        sys.exit(1)

print("Routing design...", end=' ')
if p.route_design(ROUTE_CONSTRAINTS, pnr.route_model_reader):
    print("success!")
else:
    print("failure")
    sys.exit(1)

print("Writing design to {}".format(OUTPUT_FILE))
p.write_design(pnr.write_to_xml(FABRIC_FILE, OUTPUT_FILE))