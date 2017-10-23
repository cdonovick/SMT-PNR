from enum import Enum, auto
from pnrdoctor.smt.region import Scalar, Region, Category
class Fabric:
    class Resource(Enum):
        UNSET  = 0
        Logic  = auto()
        Mem    = auto()
        IO     = auto()

        @classmethod
        def from_str(cls, str):
            if str == 'SB_IO':
                return cls.IO
            elif str == 'ICESTORM_LC':
                return cls.Logic
            elif str == 'SB_RAM40_4K':
                return cls.Mem
            else:
                raise ValueError()

    def __init__(self):
        self._rows = 18
        self._cols = 14
        self._luts = 8

        self._rows_dim = rd = Scalar('row', self.rows)
        self._cols_dim = cd = Scalar('col', self.cols)
        self._luts_dim = ld = Scalar('lut', self.luts)

        self._dims = (rd, cd, ld)

        self._region   = Region('ICE40', (rd, cd, ld), from_space=True)
        self._locations = {
                self.Resource.Logic : set(),
                self.Resource.Mem   : set(),
                self.Resource.IO    : set(),
        }

        for r in range(self.rows):
            for c in range(self.cols):
                for l in range(self.luts):
                    # nothing in the corners
                    if r in (0, self.rows-1) and c in (0, self.cols-1):
                        pass
                    # IO's
                    elif (r in (0, self.rows-1) or c in (0, self.cols-1)) and l in (0,1):
                        self.locations[self.Resource.IO].add((r,c,l))
                    # Memories
                    elif c in (3, 10):
                        self.locations[self.Resource.Mem].add((r,c,l))
                    # Logic
                    else:
                        self.locations[self.Resource.Logic].add((r,c,l))


    @property
    def rows(self):
        return self._rows

    @property
    def cols(self):
        return self._cols

    @property
    def luts(self):
        return self._luts

    @property
    def rows_dim(self):
        return self._rows_dim

    @property
    def cols_dim(self):
        return self._cols_dim

    @property
    def luts_dim(self):
        return self._luts_dim

    @property
    def locations(self):
        return self._locations

    @property
    def region(self):
        return self._region

    @property
    def dims(self):
        return self._dims
