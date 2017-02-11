'''
    Classes for represtenting designs and various constructors
'''

import itertools as it
from collections import Iterable
import z3
import traceback
from classutil import IDObject, NamedIDObject, ValidContainer

class Fabric:
    def __init__(self, dims, wire_lengths={1}, W=2, Fc=None, Fs=None, node_masks=None, model = None):
        '''
            dims := The dimensions of the fabric
            wire_lengths := the length of wires between switch boxes
            All other operands are unimplemented 
        '''
        super().__init__()
        if not isinstance(dims, Iterable):
            raise TypeError('dims must be iterable, recieved type {}'.format(type(dims)))
        dims = tuple(dims)
        
        if len(dims) != 2:
            raise ValueError('dims must be of length 2, received object of length {}'.format(len(dims)))

        self._dims = dims
        self._wire_lengths = set(wire_lengths)
        self._W = W
        self._Fc = Fc
        self._Fs = Fs
        self._model = model
        self.CLBs = {}
        self._edge_dict = {}
        

    def update_wire_lengths(self, n=2):
        for i in range(n):
            self._wire_lengths.add(max(self._wire_lengths) + 1)

    #START: Methods for routing in MonoSAT
    def setModel(self, model):
        self._model = model

    def getNode(self, pc):
        return self.CLBs[pc.pos.get_coordinates( self._model)] #return the monosat node associated with that component

    def populate_edge_dict(self, edges):
        #add all the edges to the edge dictionary (an undirected edge is represented by two directed edges)
        for e in edges:
            self._edge_dict[e.lit] = (0, e)

    def incrementEdge(self, e):
        #increments edge count
        if e.lit in self._edge_dict:
            t = self._edge_dict[e.lit]
            self._edge_dict[e.lit] = (t[0]+1, t[1])
        else:
            raise ValueError('Edge {} does not yet exist in the graph'.format(e))

    def getEdgeCount(self, e):
        return self._edge_dict[e.lit][0]

    def getMaxEdges(self):
        #returns a list of the edges which are at capacity
        #TODO maybe implement a heap-type structure eventually -- but accessing by edges is also convenient...
        max_edges = []
        for e_lit, t in self._edge_dict.items():
            count = t[0]
            edge = t[1]
            if count >= self.W:
                max_edges.append(edge)
        return max_edges
    
    def populate_CLBs(self, fab, placed_comps, g):
        '''
        add placed components to the fabric
        '''
        for pc in placed_comps:
            pcpos = pc.pos.get_coordinates(self._model)
            fab.CLBs[pcpos] = g.addNode('({},{}){}'.format(pcpos[0],pcpos[1], pc.name))

    #END: Methods for routing in MonoSAT

    @property
    def dims(self): 
        return self._dims

    @property
    def rows(self): 
        return self._dims[0]

    @property
    def cols(self): 
        return self._dims[1]
    
    @property
    def wire_lengths(self):
        return self._wire_lengths

    @property
    def W(self): 
        return self._W

    @property
    def Fc(self): 
        raise NotImplementedError('This feature is not supported')

    @property
    def Fs(self): 
        raise NotImplementedError('This feature is not supported')


class Component(NamedIDObject):
    def __init__(self, name, inputs=(), outputs=(), pos=None):
        super().__init__(name)
        self._pos = pos
        self._inputs = set(inputs)
        self._outputs = set(outputs)
        self._in_degree = 0
        self._out_degree = 0
        

    @property
    def inputs(self):
        '''
            returns a iterator over Wires
        '''
        return iter(self._inputs)
    
    @property
    def outputs(self):
        '''
            returns a iterator over Wires
        '''
        return iter(self._outputs)
    
    @property
    def pos(self):
        return self._pos

    @property
    def in_degree(self):
        return self._in_degree

    @property
    def out_degree(self):
        return self._out_degree

    @pos.setter
    def pos(self, p):
        self._pos = p
    
    def _add_input(self, src):
        self._inputs.add(src)
        self._in_degree += 1

    def _add_output(self, dst):
        self._outputs.add(dst)
        self._out_degree += 1

    def __repr__(self):
        return 'name: {}, inputs: {}, outputs: {}'.format(self.name, {x.src.name for x in self.inputs}, {x.dst.name for x in self.outputs})

class Wire(IDObject):
    def __init__(self, src, dst, width=1):
        super().__init__()
        self._src = src
        self._dst = dst
        src._add_output(self)
        dst._add_input(self)

    @property
    def src(self):
        return self._src

    @property
    def dst(self):
        return self._dst

    def __repr__(self):
        return '{} -[{}]-> {}'.format(self.src.name, self.width, self.dst.name)

class Design(NamedIDObject):
    def __init__(self, adj_dict, fabric, position_type, name='', constraint_generators=(), optimizers=()):
        '''
        adj_dict :: {str : [(str, int)]} 
        adj_dict[x] := out edges of x with the their width
        fabric :: Fabric
        position_type ::  str -> Frabric -> PositionBase

        constraints_gen :: [([Component] -> [Wire] -> fabric -> z3.Bool)]
        constraint_generators := an iterable of keys, functions that generate hard
            constraints

        optimizers :: [([Component] -> [Wire] -> fabric -> (z3.Bool, z3.Object), bool)]
        optimizers := [k, f, b] 
            where 
                k is the key
                f(components, wires) := an Iterable of functions that
                    generate hard constraint / optimizing parameters pairs, 
                b := a bool which indicating whether Optimizing parameter is minimized or maximized
        '''

        super().__init__(name)
        self._fabric = fabric
        self._position_type = position_type

        self._adj_dict = adj_dict #is kinda redundent to keep this around but it might be useful

        self._comps = dict()
        self._wires = dict()
        
        self._p_constraints = ValidContainer()
        self._cg = dict()
        self._opt = dict()

        self._max_degree = 0

        for k,f in constraint_generators:
            self.add_constraint_generator(k,f)

        for k,f,b in optimizers:
            self.add_optimizer(k,f,b)

        #build graph
        self._gen_graph()

    def _gen_graph(self):
        #reset constraints
        self._reset_constraints()

        for src_name, adj_list in self._adj_dict.items():
            if not isinstance(src_name, str):
                raise TypeError('component_graph must be a dictionary of str to [(str, int)]')

            if src_name not in self._comps:
                self._comps[src_name] = Component(src_name)
            src = self._comps[src_name]

            for pair in adj_list:
                if not isinstance(pair, tuple) or len(pair) != 2:
                    raise TypeError('component_graph must be a dictionary of str to [(str, int)]')

                dst_name = pair[0]
                width = pair[1]
                if not isinstance(dst_name, str) or not isinstance(width, int):
                    raise TypeError('component_graph must be a dictionary of str to [(str, int)]')

                if dst_name not in self._comps:
                    self._comps[dst_name] = Component(dst_name)
                dst = self._comps[dst_name]

                self._wires[(src_name, dst_name)] = Wire(src, dst, width)

        #need to generate positons for each component
        self._gen_pos()

    def _gen_pos(self):
        #reset constraints
        self._reset_constraints()
        for c in self.components:
            c.pos = self._position_type(c.name, self.fabric)
            # also find maximum (in or out) degree
            if self._max_degree < c.in_degree:
                self._max_degree = c.in_degree
            if self._max_degree < c.out_degree:
                self._max_degree = c.out_degree

    def get_sorted_components(self, out, descend):
        '''returns components sorted by their degree (out_degree if out = True, in_degree if out = False) in descending order if descend = True'''
        return sorted(list(self._comps.values()), key = lambda c: c.out_degree, reverse=descend)

    @property
    def components(self):
        return iter(self._comps.values())

    @property
    def wires(self):
        return iter(self._wires.values())

    @property
    def fabric(self):
        return self._fabric

    @fabric.setter
    def fabric(self, fabric):
        if self.fabric != fabirc:
            self._fabric = fabric
            #position representation is dependent on fabric
            self._gen_pos()

    @property
    def constraints(self):
        '''returns all hard constraints'''
        return z3.And(self.p_constraints, self.g_constraints, self.o_constraints)

    @property
    def max_degree(self):
        return self._max_degree
    
    def _reset_constraints(self):
        self._reset_p_constraints()
        self._reset_g_constraints()
        self._reset_o_constraints()

    '''
        -----------------------------------------------------------------------
        Position Related Stuff
        -----------------------------------------------------------------------
    '''

    @property
    def position_type(self):
        return self._position_type

    @position_type.setter
    def position_type(self, position_type):
        if position_type != self.position_type:
            self._position_type = position_type
            #regenerate positions for each node
            self._gen_pos()

    @property
    def p_constraints(self): 
        if not self._p_constraints.valid:
            cl = []
            for c in self.components:
                cl.append(c.pos.invariants)
            self._p_constraints.data = z3.And(*cl)

        return self._p_constraints.data

    def _reset_p_constraints(self):
        self._p_constraints.mark_invalid()
    '''
        -----------------------------------------------------------------------
        General constraints related stuff
        -----------------------------------------------------------------------
    '''
    @property
    def constraint_generators(self):
        return set((k, f) for k,(f,_) in self._cg.items()) 

    def add_constraint_generator(self, k, f):
        self._cg[k] = (f, ValidContainer())

    def remove_constraint_generator(self, k):
        del self._cg[k]

    @property
    def g_constraints(self):
        cl = []
        for k,(f, c) in self._cg.items():
            if not c.valid: 
                c.data = f(self.components, self.wires, self.fabric)
            cl.append(c.data)
        return z3.And(cl)

    def _reset_g_constraints(self):
        for _,c in self._cg.values():
            c.mark_invalid()

    '''
        -----------------------------------------------------------------------
        Optimization Related Stuff
        -----------------------------------------------------------------------
    '''
        
    @property
    def optimizers(self):
        return set((k, f, b) for k,(f,_,b) in self._cg.items())

    def add_optimizer(self, k, f, minimize):
        self._opt[k] = (f, ValidContainer(), minimize)

    def remove_optimizer(self, k):
        del self._opt[k]

    @property 
    def o_constraints(self):
        cl = []
        for f,c,m in self._opt.values():
            # f := functiom
            # c := ValidContainer(constraints, parameter)
            # m := minimize flag
            if not c.valid:
                c.data = f(self.components, self.wires, self.fabric)
            if c.data[0]:
                #check that list nonempty to avoid appending an empty list
                cl.append(c.data[0]) 
        return z3.And(cl)

    @property
    def opt_parameters(self): 
        cl = []
        for f,c,m in self._opt.values():
            # f := functiom
            # c := ValidContainer(constraints, parameter)
            # m := minimize flag
            if not c.valid:
                c.data = f(self.components, self.wires, self.fabric)
            cl.append((c.data[1], m))
        return cl

    def _reset_o_constraints(self):
        for _,c,_ in self._opt.values():
            c.mark_invalid()
