import z3
import z3util as zu
import constraints
from design import Design, Fabric
import position


def tiny_test(dims=(3,3), debug_prints=True):
    ''' 
        place 4 nodes on a 3x3 fabric [with length 1 wires] 
    '''
    adj = {'n1' : [('n2', 1),('n3',1)], 'n2' : [('n4',1)], 'n3' : [('n4',1)], 'n4' : {}}
    fab = Fabric((3,3), wire_lengths={1})
    if debug_prints: print('Built fabric {}'.format(fab))

    des = Design(adj, fab, position.Unpacked2H)
    if debug_prints: print('Built design {}'.format(des))

    des.add_constraint_generator(constraints.nearest_neighbor)
    des.add_constraint_generator(constraints.distinct)

    sol = run_test(des, debug_prints)
    return des, fab, sol

#
#def small_test(dims=(8,8), debug_prints=True):
#    '''
#        place a depth 5 binary tree on a 8 by 8 [with length 2,3 wires] 
#    ''' 
#    adj = {'n{}'.format(i) : frozenset(('n{}'.format(2*i), 'n{}'.format(2*i+1))) for i in range(1,2**4)}
#    run_test(adj, dims, {}, debug_prints)
#
#
#def unsat_test(debug_prints=True):
#    adj = {'n1' : {'n2','n3','n4','n5','n6'}}
#    run_test(adj, (4,4), {1}, debug_prints)
#

def run_test(design, debug_prints):
    if debug_prints: print('running test')
    
    s = z3.Solver()
    s.add(design.constraints)
    if s.check() != z3.sat:
        if debug_prints:
            print('test is unsat')
    elif debug_prints:
        model_printer(s.model(), design)
    return s
        

def model_printer(model, design):
    mesh = dict()
    for c in design.components:
        xy = c.pos.get_coordinates(model)
        mesh[xy] = c.name
        print(c.name, ':', xy)
    print()
    print(mesh)
    print()
    s = []
    for y in range(design.fabric.dims[1]):
        ss = []
        for x in range(design.fabric.dims[0]):
            if (x,y) in mesh:
                ss.append(mesh[(x,y)])
            else:
                ss.append('-')
        s.append(ss)
    s = map(' '.join, s)
    s = '\n'.join(s)
    print(s)

        

