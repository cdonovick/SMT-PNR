import fabric
'''
   Functions to be used in fabric.py
'''

def getSide(side_str):
    '''
       Takes a string and returns the corresponding side
    '''
    if side_str == 'N':
        return fabric.Side.N
    elif side_str == 'S':
        return fabric.Side.S
    elif side_str == 'E':
        return fabrci.Side.E
    elif side_str == 'W':
        return fabric.Side.W
    elif side_str == 'NS':
        return fabric.Side.NS
    else:
        raise ValueError('Not passed a valid side string')

def mapSide(x, y, side):
    '''
       Given a location and a side, returns the receiving tile location and receiving side
    '''
    if side is fabric.Side.N:
        return x, y+1, fabric.Side.S
    elif side is fabric.Side.S:
        return x, y-1, fabric.Side.N
    elif side is fabric.Side.E:
        return x+1, y, fabric.Side.W
    elif side is fabric.Side.W:
        return x-1, y, fabric.Side.E
    else:
        raise ValueError('Expected a fabric.Side but got {}'.format(type(side)))


def parse_name(text):
    '''
        Takes a (non-PE) port name and returns direction, BUS width, side, track number
    '''
    s = text.split('_')
    return s[0], s[1], fabric.Side(int(s[2][1])), int(s[3][1])
