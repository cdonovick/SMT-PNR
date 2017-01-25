
def tiny_test(dims=(3,3), debug_prints=True):
    ''' 
        place 4 nodes on a 3x3 fabric [with length 1 wires] 
    '''
    adj = {'n1' : {'n2','n3'}, 'n2' : {'n4'}, 'n3' : {'n4'}, 'n4' : {}}
    run_test(adj, dims, {}, debug_prints)


def small_test(dims=(8,8), debug_prints=True):
    '''
        place a depth 5 binary tree on a 8 by 8 [with length 2,3 wires] 
    ''' 
    adj = {'n{}'.format(i) : frozenset(('n{}'.format(2*i), 'n{}'.format(2*i+1))) for i in range(1,2**4)}
    run_test(adj, dims, {}, debug_prints)


def unsat_test(debug_prints=True):
    adj = {'n1' : {'n2','n3','n4','n5','n6'}}
    run_test(adj, (4,4), {1}, debug_prints)

