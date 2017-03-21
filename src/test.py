#!/usr/bin/env python3
import design, design.core2graph, fabric, pnr, smt
FABRIC_FILE = '../demo_cgra4x4.xml'
DESIGN_FILE = '../add.json'
OUTPUT_FILE = '../demo_placed.xml'

POSITION_T = smt.BVXY
PLACE_CONSTRAINTS = pnr.init_positons(POSITION_T), pnr.distinct, pnr.nearest_neighbor,
ROUTE_CONSTRAINTS = pnr.build_msgraph, pnr.excl_constraints, pnr.reachability, #pnr.dist_limit(1.5)


d = design.Design(*design.core2graph.load_core(DESIGN_FILE))
f = fabric.parseXML(FABRIC_FILE)
p = pnr.PNR(f, d)

p.place_design(PLACE_CONSTRAINTS, pnr.place_model_reader)
p.route_design(ROUTE_CONSTRAINTS, pnr.route_model_reader)
print(p._place_state)
print(p._route_state)
p.write_design(pnr.write_to_xml(FABRIC_FILE, OUTPUT_FILE))



