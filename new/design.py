'''
    Classes for represtenting designs and various constructors
'''

import itertools as it
from collections import Iterable
import z3
import traceback

_object_id = it.count().__next__

class IDObject:
    def __init__(self):
        self._id = _object_id()

    def __eq__(self, other):
        return isinstance(other, type(self)) and self._id == other._id

    def __ne__(self, other):
        return not isinstance(other, type(self)) or not self._id == other._id
 
    def __hash__(self):
        return hash(self._id)


    @property
    def id(self):
        return self._id
    
class NamedIDObject(IDObject):
    def __init__(self, name):
        super().__init__()
        self._name = '{}_{}'.format(name, self.id)

    @property
    def name(self):
        return self._name

class Fabric:
    def __init__(self, dims, wire_lengths={1}, W=None, Fc=None, Fs=None, node_masks=None):
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

    def update_wire_lengths(self, n=2):
        for i in range(n):
            self._wire_lengths.add(max(self._wire_lengths) + 1)

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


class Component(NamedIDObject):
    def __init__(self, name, inputs=(), outputs=(), pos=None):
        super().__init__(name)
        self._pos = pos
        self._inputs = set(inputs)
        self._outputs = set(outputs)
        

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

class _valid_container:
    '''wrapper class that allows data to marked invalid '''
    __slots__ = '_data', '_valid'

    def __init__(self):
        self.mark_invalid()

    def mark_invalid(self):
        self._valid = False

    @property
    def valid(self):
        return self._valid 

    @property
    def data(self):
        if not self.valid:
            raise AttributeError('Data is invalid')
        return self._data

    @data.setter
    def data(self, data):
        self._valid = True
        self._data = data

    def __repr__(self):
        if self.valid:
            return repr(data)
        else:
            return 'Invalid'

class Design(NamedIDObject):
    def __init__(self, adj_dict, fabric, position_type, name='', constraint_generators=(), optimizers=()):
        '''
        adj_dict :: {str : [(str, int)]} 
        adj_dict[x] := out edges of x with the their width
        fabric :: Fabric
        position_type ::  str -> Frabric -> PositionBase

        constraints_gen :: [([Component] -> [Wire] -> fabric -> z3.Bool)]
        constraint_generators := an iterable of functions that generate hard
            constraints

        optimizers :: [([Component] -> [Wire] -> fabric -> (z3.Bool, z3.Object), bool)]
        optimizers := [f, b] 
            where 
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
        
        self._p_constraints = _valid_container()
        self._cg = dict()
        self._opt = dict()

        for f in constraint_generators:
            self.add_constraint_generator(f)

        for f,b in optimizers:
            self.add_optimizer(f,b)

        #build graph
        self._gen_graph()

    def _gen_graph(self):
        #all constraints depend on the graph
        self._reset_p_constraints()
        self._reset_g_constraints()
        self._reset_o_constraints()


        for src_name, adj_list in self._adj_dict.items():
            if not isinstance(src_name, str):
                raise TypeError('component_graph must be a dictionary of str to [(str, int)]')

            if src_name not in self._comps:
                self._comps[src_name] = Component(src_name)
            src = self._comps[src_name]


            for pair in adj_list:
                dst_name = pair[0]
                width = pair[1]
                if not isinstance(dst_name, str):
                    raise TypeError('component_graph must be a dictionary of str to [(str, int)]')
                
                if dst_name not in self._comps:
                    self._comps[dst_name] = Component(dst_name)
                dst = self._comps[dst_name]

                self._wires[(src_name, dst_name)] = Wire(src, dst, width)

        #need to generate positons for each component
        self._gen_pos()

    def _gen_pos(self):
        #reset position constraints
        self._reset_p_constraints()
        for c in self.components:
            c.pos = self._position_type(c.name, self.fabric)


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
        #return z3.And(self.p_constraints, self.g_constraints)

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
        return set(self._cg)

    def add_constraint_generator(self, f):
        self._cg[f] = _valid_container()

    def remove_constraint_generator(self, f):
        del self._cg[f]

    @property
    def g_constraints(self):
        cl = []
        for f,c in self._cg.items():
            if not c.valid: 
                c.data = f(self.components, self.wires, self.fabric)
            cl.append(c.data)
        return z3.And(*cl)

    def _reset_g_constraints(self):
        for f in self.constraint_generators:
            self._cg[f].mark_invalid()

    '''
        -----------------------------------------------------------------------
        Optimization Related Stuff
        -----------------------------------------------------------------------
    '''
        
    @property
    def optimizers(self):
        return set(self._opt)

    def add_optimizer(self, f, minimize):
        self._opt[f] = (_valid_container(), minimize)

    def remove_optimizer(self, f):
        del self._opt[f]

    @property 
    def o_constraints(self):
        cl = []
        for f,c in self._opt.items():
            # c[0] := _valid_container(constraints, parameter)
            # c[1] := minimize flag
            if not c[0].valid:
                c[0].data = f(self.components, self.wires, self.fabric)
            cl.append(c[0].data[0]) 
        return z3.And(*cl)

    @property
    def opt_parameters(self): 
        cl = []
        for f,c in self._opt.items():
            # c[0] := _valid_container(constraints, parameter)
            # c[1] := minimize flag
            if not c[0].valid:
                c[0].data = f(self.components, self.wires, self.fabric)
            cl.append((c[0].data[1], c[1]))
        return cl

    def _reset_o_constraints(self):
        for f in self.optimizers:
            self._opt[f][0].mark_invalid()
