from collections import namedtuple

from pnrdoctor.fabric.fabricutils import muxindex
from pnrdoctor.design.module import Resource

# see fabric.fabricutils for muxindex documentation

configindex = namedtuple('configindex', 'ps resource')

def get_muxindices(tie, p_state):
    '''
       Convenience function for getting the muxindices of the src and dst
       of a tie
    '''

    src_index = get_muxindex(tie.src, p_state, tie.width, tie.src_port)
    dst_index = get_muxindex(tie.dst, p_state, tie.width, tie.dst_port)

    return src_index, dst_index


def get_muxindex(mod, p_state, layer, port=None):
    '''
       Given a module, p_state and the layer, returns the muxindex for indexing
       into the fabric
    '''

    # if there's a register, don't grab the track, if it's anything else, it doesn't matter
    d = {'ps': p_state[mod][0][:2], 'bw': layer}

    if mod.resource != Resource.Reg:
        assert port is not None
        return muxindex(resource=mod.resource, port=port, **d)
    else:
        # this is a register
        # for now, fabric uses Resource.SB everywhere -- not Resource.Reg
        assert mod.resource == Resource.Reg
        assert len(p_state[mod]) == 2, 'Expected Pself and Pother for register position'
        return muxindex(resource=Resource.SB, po=p_state[mod][1][:-1],
                        track=p_state[mod][0][-1], **d)


def process_regs(design, p_state, fabric):
    for mod in design.modules:
        if mod.resource == Resource.Reg:
            # could have multiple outputs, for now just taking random
            # this is heuristic anyway
            for tie in mod.outputs.values():
                if tie.dst in p_state:
                    outmod = tie.dst
                    dst_port = tie.dst_port

            modpos = p_state[mod][0][:-1]
            # get just the position (registers have extra info)
            outmodpos = p_state[outmod][0][0:2]

            vertport = None
            if outmod.resource == Resource.PE:
                # hacky hardcoding port names
                vertport = dst_port in {'a', 'c'}

            # take port into consideration because of vertical/horizontal track issue
            pother = _reg_heuristic(modpos, outmodpos, vertport)
            # hacky assuming planar tracks
            p_state[mod] = pother + (p_state[mod][0][-1],)

            regindex = get_muxindex(mod, p_state, tie.width)

            # now split that port
            origport = fabric[regindex].source
            # assert that the port hasn't already been split
            assert origport == fabric[regindex].sink

            snkport, srcport = origport.split()
            # note: for now still indexing by assigned location
            fabric[regindex].source = srcport
            fabric[regindex].sink = snkport
            del origport


def _reg_heuristic(pos1, pos2, vertport):
    '''
       Given two positions, returns the other position
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
         side of the switch box, thus the return value is (1, 0)
    '''
    difx = pos2[0] - pos1[0]
    dify = pos2[1] - pos1[1]

    if vertport is not None:
        if vertport:
            if dify <= 0 and pos1[1] > 0:
                return (pos1[0], pos1[1]-1)
            else:
                return (pos1[0], pos1[1]+1)
        else:
            if difx <= 0 and pos1[0] > 0:
                return (pos1[0] - 1, pos1[1])
            else:
                return (pos1[0] + 1, pos1[1])
    else:
        # pick by largest difference
        if abs(difx) >= abs(dify):
            if difx <= 0 and pos1[0] > 0:
                return (pos1[0]-1, pos1[1])
            else:
                return (pos1[0]+1, pos1[1])
        else:
            if dify <= 0 and pos1[1] > 0:
                return (pos1[0], pos1[1]-1)
            else:
                return (pos1[0], pos1[1]+1)
