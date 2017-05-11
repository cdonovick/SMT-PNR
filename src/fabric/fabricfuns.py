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
