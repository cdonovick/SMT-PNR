'''
   Functions to be used in fabric.py
'''
from enum import Enum

class Side(Enum):
    N = 3
    S = 1
    E = 0
    W = 2
    PE = 4 #no side

def getSide(side_str):
    '''
       Takes a string and returns the corresponding side
    '''
    if side_str == 'N':
        return Side.N
    elif side_str == 'S':
        return Side.S
    elif side_str == 'E':
        return fabrci.Side.E
    elif side_str == 'W':
        return Side.W
    elif side_str == 'NS':
        return Side.NS
    else:
        raise ValueError('Not passed a valid side string')

def mapSide(x, y, side):
    '''
       Given a location and a side, returns the receiving tile location and receiving side
    '''
    if side is Side.N:
        return x, y-1, Side.S
    elif side is Side.S:
        return x, y+1, Side.N
    elif side is Side.E:
        return x+1, y, Side.W
    elif side is Side.W:
        return x-1, y, Side.E
    else:
        raise ValueError('Expected a Side but got {}'.format(type(side)))


def parse_name(text):
    '''
        Takes a (non-PE) port name and returns direction, BUS width, side, track number
    '''
    s = text.split('_')
    return s[0], s[1], Side(int(s[2][1])), int(s[3][1])


def parse_mem_tile_name(text):
    '''
       Parses the mem_tile wire format
       Returns direc, bus_width, side, track, row_incr
    '''
    s = text.split('_')
    return s[0], s[2], Side(int(s[3])), int(s[4]), s[1]


def pos_to_side(pos1, pos2, vertport):
    '''
       Given two positions, returns the output side from pos1's perspective
       For use in preprocessing registers for routing
       Example: 
          pos1 = (0,0)
          pos2 = (1,0)
         i.e. for r with pos1 and m with pos2 on a 4x4
          r  m x x
          x  x  x x
          x  x  x x
          x  x  x x
        
         Then the resulting side is East, because the register (r) should be placed on the east
         side of the switch box
    '''
    difx = pos2[0] - pos1[0]
    dify = pos2[1] - pos1[1]
    
    # TODO: Improve this heuristic for NW, SW etc...
    if vertport is not None:
        if vertport:
            if dify >= 0:
                return Side.S
            else:
                return Side.N
        else:
            if difx >= 0:
                return Side.E
            else:
                return Side.W
    else:
        # pick by largest difference
        if abs(difx) >= abs(dify):
            if difx >= 0:
                return Side.E
            else:
                return Side.W
        else:
            if dify >= 0:
                return Side.S
            else:
                return Side.N

    # For some reason this is less robust
    # makes no sense because only changes is handling edge cases...
    
    # if vertport is not None:
    #     if vertport:
    #         if dify <= 0 and pos1[1] > 0:
    #             return Side.N
    #         else:
    #             return Side.S
    #     else:
    #         if difx <= 0 and pos1[0] > 0:
    #             return Side.W
    #         else:
    #             return Side.E
    # else:
    #     # pick by largest difference
    #     if abs(difx) >= abs(dify):
    #         if difx <= 0 and pos1[0] > 0:
    #             return Side.W
    #         else:
    #             return Side.E
    #     else:
    #         if dify <= 0 and pos1[1] > 0:
    #             return Side.N
    #         else:
    #             return Side.S


    # Unfinished: Need to take port into consideration because of vertical/horizontal track issues
