'''
    Classes for represtenting designs and various constructors
'''

""" TODO:
        constraint_generators needs some sort of map from the function to the generated contraints
"""

import itertools as it
from collections import Iterable
import z3

COMP_X    = 1
COMP_Y    = 1
COMP_AREA = __COMP_X * __COMP_Y

__object_id = it.count().next

class IDObject:
    def __init__(self):
        self._id = __object_id()

    def __eq__(self, other):
        return isinstance(other, type(self)) and self._id == other._id

    def __ne__(self, other):
        return not isinstance(other, type(self)) or not self._id == other._id
 
    def __hash__(self):
        return hash(self._id)

    @property
    def id(self):
        return self._id
    

class Fabric:
    def __init__(self, dims, wire_lengths={1}, W=None, Fc=None, Fs=None, node_masks=None):
        '''
            dims := The dimensions of the fabric
            wire_lengths := the length of wires between switch boxes
            All other operands are unimplemented 
        '''

        if not isinstance(dims, Iterable):
            raise TypeError('dims must be iterable, recieved type {}'.format(type(dims)))
        dims = tuple(dims)
        
        if len(dims) != 2:
            raise ValueError('dims must be of length 2, received object of length {}'.format(len(dims)))

        self._dims = dims
        welf._wire_lengths = frozenset(wire_lengths)
        self._W = W
        self._Fc = Fc
        self._Fs = Fs

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
        raise NotImplementedError('This feature is not supported')

    @property
    def Fc(self): 
        raise NotImplementedError('This feature is not supported')

    @property
    def Fs(self): 
        raise NotImplementedError('This feature is not supported')


class Component(IDObject):
    def __init__(self, name, inputs=(), outputs=(), pos=None):
        self._name = name
        self._pos = pos
        self._inputs = set(inputs)
        self._outputs = set(outputs)
        
    @property
    def name(self):
        return self._name

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

    @pos.setter
    def pos(self, p):
        self._pos = p
    
    def _add_input(self, src):
        self._inputs.add(src)

    def _add_output(self, dst):
        self._outputs.add(dst)

    def __repr__(self):
        return 'name: {}, inputs: {}, outputs: {}'.format(self.name, {x.src.name for x in self.inputs}, {x.dst.name for x in self.outputs})

class Wire(IDObject):
    def __init__(self, src, dst, width=1):
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

class Design(IDObject):
    def __init__(self, adj_dict, fabric, position_type, constraint_generators=None, optimizer=None):
        '''
        adj_dict :: {str : [(str, int)]} 
        adj_dict[x] := out edges of x with the their width
        fabric :: Fabric
        position_type ::  str -> Frabric -> PositionBase

        constraints_gen :: [([Component] -> [Wire] -> fabric -> z3.Bool)]
        constraint_generators := an iterable of functions that generate hard constraints

        constraints_opt :: [Component] -> [Wire] -> fabric -> (z3.Bool, z3.Object)
        constraints_opt(components, wires) := (constraint, paramterer to be optimized)
        '''

        self._name = name
        self._fabric = fabric
        self._position_type = position_type

        self._adj_dict = adj_dict #is kinda redundent to keep this around but it might be useful

        self._comps = dict()
        self._wires = dict()

        for f in constraint_generators:
            self._cg[f] = None

        self._opt = optimizer
        
        #build graph
        self._gen_graph()

    def _gen_graph(self):
        #all constraints depend on the graph
        self._reset_p_constraints()
        self._reset_g_constraints()
        self._reset_o_constraints()


        for src_name, adj_list in self._adj_dict.items():
            if not isinstance(src_name, str):
                raise TypeError('component_graph must be a dictionary of str to str')

            if src_name not in self._comps:
                self._comps[src_name] = Component(src_name)
            src = self._comps[src_name]


            for dst_name, width in adj_list:
                if not isinstance(dst_name, str):
                    raise TypeError('component_graph must be a dictionary of str to str')
                
                if dst_name not in self._comps:
                    self._comps[dst_name] = Component(dst_name)
                dst = self._comps[dst_name]

                self._wires[(src_name, dst_name)] = Wire(src, dst, width)

        #need to generate positons for each component
        self._gen_pos()

    def _gen_pos(self):
        #reset position constraints
        self._p_constraints(self)

        for c in self.components:
            c.pos = self._position_type(c.name, self.fabric)


    def _reset_p_constraints(self):
        self._p_constraints = None

    def _reset_g_constraints(self):
        for f in self.constraint_gerators:
            self._cg[f] = None 


    def _reset_o_constraints(self):
        self._o_constraints = None
        self._opt_parameter = None

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
    def position_type(self):
        return self._position_type

    @position_type.setter
    def position_type(self, position_type):
        if position_type != self.position_type:
            self._position_type = position_type
            #regenerate positions for each node
            self._gen_pos()
    
    @property
    def constraint_generators(self):
        return frozenset(self._cg)

    def add_constraint_generator(self, f):
        self._cg[f] = None

    def remove_constraint_generator(self, f):
        del self._cg[f]

        
    @property
    def optimizer(self):
        return self._opt

    @optimizer.setter
    def optimizer(self, optimizer):
        if optimizer != self.optimizer:
            self._o_constraints = None
            self._opt_parameter = None
            self._opt = optimizer

    @property
    def p_constraints(self):
        #constraints are not generated
        if self._p_constraints is None:
            self._p_constraints = z3.And(*(c.pos.invariants for c in self.components))

        return self._p_constraints
    
    @property
    def g_constraints(self):
        if not self.constraints_gen:
            raise AttributeError('Design does not have any assoicated constraint_generators')

        cl = []
        for f,c in self._cg.items():
            if c is None: 
                self._cg[f] = f(self.components, self.wires, self.fabric)
            cl += self._cg[f]

        return z3.And(*cl)

    @property 
    def o_constraints(self):
        if self.optimizer is None:
            raise AttributeError('Design does not have an assoicated optimizer')

        if self._o_constraints is None:
            self._o_constraints, self._opt_parameter = self.optimizer(self.components, self.wires, self.fabric)
        
        return self._o_constraints


    @property
    def opt_parameter(self):
        if self.optimizer is None:
            raise AttributeError('Design does not have an assoicated optimizer')

        if self._o_constraints is None:
            self._o_constraints, self._opt_parameter = self.optimizer(self.components, self.wires, self.fabric)
        
        return self._o_constraints

