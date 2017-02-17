import dot2smt
import time
import position
import constraints
import design
import math
import z3
from collections import defaultdict

files = []
files.append('../examples/downCast_13_reduce.dot')
files.append('../examples/downCast_15_reduce.dot')
files.append('../examples/lambda_arris_v3lua_line43_10_reduce.dot')
files.append('../examples/NMS_10_reduce.dot')
files.append('../examples/Resp_5_reduce.dot')


def bvxy_test(filepath, dims=(10,10), debug_prints=True):
    adj = dot2smt.from_file(filepath)
    fab = design.Fabric(dims)
    des = design.Design(adj, fab, position.BVXY)
    des.add_constraint_generator('distinct', constraints.distinct)
    neighborhood = int(math.ceil(des.max_degree/4))
    des.add_constraint_generator('neighborhood', constraints.in_neighborhood(neighborhood))
    sol = run_test(des, debug_prints)
    return des, fab, sol

def run_test(design, debug_prints):
    if debug_prints: print('running test')
    s = z3.Solver()

    s.add(design.constraints)
    start_time = time.time()
    result = s.check()
    end_time = time.time()
    print('It took {}s to place'.format(end_time-start_time))
    if debug_prints:
        if result != z3.sat:
            print('test is unsat')
        else:
            print('test is sat')
            model_printer(s.model(), design)
    else:
        s.check()

    return s

def model_printer(model, design):
    mesh = defaultdict(lambda: '-')
    for c in design.components:
        (x, y) = c.pos.get_coordinates(model)
        mesh[(x,y)] = c.name

    width = 2 + max(len(n) for n in mesh.values())
    s = []
    for y in range(design.fabric.dims[1]):
        ss = []
        for x in range(design.fabric.dims[0]):
            ss.append('{c: ^{w}}'.format(c=mesh[(x, y)], w=width))
        s.append(ss)
    s = map(' '.join, s)
    s = '\n'.join(s)
    print(s)



def test():
    print('Test with varying neighborhoods:')
    for f in files:
        print('On file: ', f)
        adj = dot2smt.from_file(f)
        ncomps = 0
        nconns = 0
        for a in adj:
            ncomps += 1
            for b in adj[a]:
                nconns += 1
        print('Has {} components and {} connections'.format(ncomps, nconns))
        bvxy_test(f)
