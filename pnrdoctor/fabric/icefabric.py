from enum import Enum, auto
from pnrdoctor.smt.region import Scalar, Region

class IceStick:
    def __init__(self):
        self._rows = 18
        self._cols = 18
        self._luts = 8


        self._rows_dim = Scalar('row', self.rows)
        self._cols_dim = Scalar('col', self.cols)
        self._luts_dim = Scalar('lut', self.luts)
        self._locations = {
                IceResource.Logic : set(),
                IceResource.Mem   : set(),
                IceResource.IO    : set(),
        }

        for r in range(self.rows):
            for c in range(self.cols):
                for l in range(self.luts):
                    # nothing in the corners
                    if r in (0, self.rows-1) and c in (0, self.cols-1):
                        continue

                    # IO's
                    if (r in (0, self.rows-1) or c in (0, self.cols-1)) and l == 0:
                        self.locations[IceResource.IO].add((r,c,l))
                        continue

                    # Memories
                    if c in (3, 10):
                        self.locations[IceResource.Mem].add((r,c,l))
                        continue

                    # Logic
                    self.locations[IceResource.Logic].add((r,c,l))


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


class IceResource(Enum):
    Logic  = Auto()
    Mem    = Auto()
    IO     = Auto()

